module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle002
public import ReciprocityTheory.DualLattices.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW.SpanModel

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def leftInv (E : Type) [Field E] [NumberField E] (a : ℕ) : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | ∀ γ g, F (ratGL E a γ * g) = F g}
  add_mem' hF hG γ g := by simp [hF γ g, hG γ g]
  zero_mem' _ _ := rfl
  smul_mem' c F hF γ g := by simp [hF γ g]

end GlobalTheory.JSW.SpanModel
end
end

section

noncomputable section

open WittVector Ideal Matrix

namespace GlobalTheory.Sandwich.Model

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem xi_eq (ε : PreTilt O p) : xi ε = ReciprocityTheory.PGsh.Ainf.xi p O ε := rfl

theorem nu_eq (ε : PreTilt O p) : nu ε = ReciprocityTheory.PGsh.Ainf.nu p O ε := rfl

section Field

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε

theorem theta_mu : fontaineTheta O p (mu ε) = 0 := by
  rw [← xi_mul_nu, map_mul, xi_eq, ReciprocityTheory.PGsh.Ainf.theta_xi p O hv ε hε, zero_mul]

theorem mu_ne_zero : mu ε ≠ 0 := by
  intro h
  rw [← xi_mul_nu, mul_comm] at h
  have := ReciprocityTheory.PGsh.Ainf.xi_nzd p O hv ε hε _ h
  exact ReciprocityTheory.PGsh.Ainf.theta_nu p O hv ε hε (by rw [← nu_eq, this, map_zero])

omit hε [IsAlgClosed C] in
theorem isDomain_Ainf : IsDomain (Ainf p O) := by
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  infer_instance

variable {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (D : Datum ε h Λ)

end Field

end GlobalTheory.Sandwich.Model
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

section Bi

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  {E E' E'' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E'] [AddCommGroup E''] [Module k E'']


variable (k ι κ E'') in
def biD : (Finset ι × Finset κ → E'') →ₗ[k] (Finset ι × Finset κ → E'') :=
  LinearMap.pi fun x =>
    (∑ i ∈ x.1, GlobalTheory.cubeSign x.1 i • LinearMap.proj (R := k) (φ := fun _ : Finset ι × Finset κ => E'') (x.1.erase i, x.2)) +
      ((-1 : ℤ) ^ (x.1.card + 1)) •
        ∑ j ∈ x.2, GlobalTheory.cubeSign x.2 j • LinearMap.proj (R := k) (φ := fun _ : Finset ι × Finset κ => E'') (x.1, x.2.erase j)

def bicechC (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E') (n : ℤ) :
    Submodule k (Finset ι × Finset κ → E'') :=
  Submodule.pi Set.univ fun x =>
    if x.1.Nonempty ∧ x.2.Nonempty ∧ ((x.1.card + x.2.card : ℕ) : ℤ) = n + 2 then Submodule.map₂ μ (A x.1) (B x.2) else ⊥

def bicech (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E') :
    Cx k (Finset ι × Finset κ → E'') :=
  ⟨bicechC μ A B, biD k ι κ E''⟩

def boxC (μ : E →ₗ[k] E' →ₗ[k] E'') (a : Finset ι → E) (b : Finset κ → E') : Finset ι × Finset κ → E'' :=
  fun x => μ (a x.1) (b x.2)


end Bi

end GlobalTheory.PD
end
end

section

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR

namespace GlobalTheory.PD

section Proj

variable (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} (x : Fin (d + 1) → F)

structure IsPd : Prop where
  ne : ∀ i, x i ≠ 0
  indep : AlgebraicIndependent k fun j : Fin d => x j.succ / x 0
  gen : IntermediateField.adjoin k (Set.range fun j : Fin d => x j.succ / x 0) = ⊤

def rA (I : Finset (Fin (d + 1))) : Subalgebra k F := Algebra.adjoin k {y | ∃ i ∈ I, ∃ j, y = x j / x i}

def tw (m : ℤ) (I : Finset (Fin (d + 1))) : Submodule k F :=
  ⨅ i ∈ I, (Subalgebra.toSubmodule (rA k x I)).comap (LinearMap.mulLeft k ((x 0 / x i) ^ m))

def omA (I : Finset (Fin (d + 1))) : Submodule k F :=
  ⨅ i ∈ I, (Subalgebra.toSubmodule (rA k x I)).comap (LinearMap.mulLeft k (∏ j, x i / x j))

def IsRes (ρ : F →ₗ[k] k) : Prop := ρ 1 = 1 ∧ ∀ m : Fin (d + 1) → ℤ, ∑ j, m j = 0 → m ≠ 0 → ρ (∏ j, x j ^ m j) = 0

variable {W W' : Type} [AddCommGroup W] [Module F W] [Module k W] [IsScalarTower k F W]
  [AddCommGroup W'] [Module F W'] [Module k W'] [IsScalarTower k F W']

structure IsBundle (L : Finset (Fin (d + 1)) → Submodule k W) : Prop where
  fg : ∀ i, ∃ s : Finset W, L {i} = (Submodule.span (rA k x {i}) (s : Set W)).restrictScalars k ∧ Submodule.span F (s : Set W) = ⊤
  proj : ∀ i, Module.Projective (rA k x {i}) (Submodule.span (rA k x {i}) (L {i} : Set W))
  loc : ∀ I, ∀ i ∈ I, L I = (Submodule.span (rA k x I) (L {i} : Set W)).restrictScalars k

def kpair (ρ : F →ₗ[k] k) (β : W →ₗ[F] W' →ₗ[F] F) : W →ₗ[k] W' →ₗ[k] k := (β.restrictScalars₁₂ k k).compr₂ ρ

end Proj

section Forms

variable (k : Type) [Field k] (K : Type) [Field K] [Algebra k K]

def omB (B : Subalgebra k K) (q : ℕ) : Submodule k (DR k K) :=
  Submodule.span k {y | ∃ b ∈ B, ∃ v : Fin q → K, (∀ j, v j ∈ B) ∧ y = b • ExteriorAlgebra.ιMulti K q fun j => D k K (v j)}

def trunc (b : ℕ) : DR k K →ₗ[k] DR k K :=
  ∑ q ∈ Finset.range b, (GradedAlgebra.proj (fun i : ℕ => ⋀[K]^i Ω[K⁄k]) q).restrictScalars k

def sg : DR k K →ₐ[k] DR k K := (sgn (R := k) (B := K)).restrictScalars k

variable {K} {ι : Type} [LinearOrder ι]

def tot (B : Finset ι → Subalgebra k K) (a b : ℕ) : Cx k (Finset ι → DR k K) :=
  ⟨totC (fun q s => omB k K (B s) q) a b, totD (trunc k K b ∘ₗ dDR k K)⟩

variable (K) {F : Type} [Field F] [Algebra k F] [Algebra F K] [IsScalarTower k F K] {d : ℕ} (x : Fin (d + 1) → F)

def rB (I : Finset (Fin (d + 1))) : Subalgebra k K := (integralClosure (rA k x I) K).restrictScalars k

structure IsFinCover : Prop where
  pd : IsPd k x
  fin : FiniteDimensional F K
  smooth : ∀ i, Algebra.Smooth k (rB k K x {i})

  [sep : Algebra.IsSeparable F K]

def vol0 : DR k K :=
  ExteriorAlgebra.ιMulti K d fun j => (algebraMap F K (x j.succ / x 0))⁻¹ • D k K (algebraMap F K (x j.succ / x 0))

def IsTop (τ : DR k K →ₗ[K] K) : Prop := τ (vol0 k K x) = 1 ∧ ∀ q, q ≠ d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], τ y = 0


variable {K} in
def trF (τ : DR k K →ₗ[K] K) (ρ : F →ₗ[k] k) : DR k K →ₗ[k] k :=
  ρ ∘ₗ (Algebra.trace F K).restrictScalars k ∘ₗ τ.restrictScalars k

def hyp : Finset (Fin (d + 1)) → DR k K := fun s =>
  ∑ i ∈ s, ∑ j ∈ s, if s.card = 2 ∧ i < j then (algebraMap F K (x j / x i))⁻¹ • ι1 (D k K (algebraMap F K (x j / x i))) else 0

end Forms

section API

variable {k : Type} [Field k] {K : Type} [Field K] [Algebra k K] {F : Type} [Field F] [Algebra k F] [Algebra F K]
  [IsScalarTower k F K] {d : ℕ} {x : Fin (d + 1) → F}

theorem IsFinCover.of_charZero [CharZero F] (pd : IsPd k x) (fin : FiniteDimensional F K)
    (smooth : ∀ i, Algebra.Smooth k (rB k K x {i})) : IsFinCover k K x := by
  have := fin
  have : Algebra.IsSeparable F K := inferInstance
  exact ⟨pd, fin, smooth⟩


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem IsFinCover.exists_basis (h : IsFinCover k K x) :
    ∃ b : Module.Basis (Fin d) K Ω[K⁄k], ∀ j, b j = D k K (algebraMap F K (x j.succ / x 0)) := by
  have := h.fin
  have := h.sep
  let t : Fin d → F := fun j => x j.succ / x 0
  let A := MvPolynomial (Fin d) k
  let : Algebra A F := (MvPolynomial.aeval t).toRingHom.toAlgebra
  have : IsScalarTower k A F := IsScalarTower.of_algebraMap_eq fun r =>
    ((MvPolynomial.aeval t).commutes r).symm
  have hinj : Function.Injective (algebraMap A F) := h.pd.indep
  have : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective A F).mpr hinj
  have : IsFractionRing A F := IsFractionRing.of_field A F fun z => by
    have hz : z ∈ IntermediateField.adjoin k (Set.range t) := by
      rw [h.pd.gen]; exact IntermediateField.mem_top
    obtain ⟨r, hr, s, hs, rfl⟩ := (IntermediateField.mem_adjoin_iff_div (F := k) (S := Set.range t)).mp hz
    rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range] at hr hs
    obtain ⟨p, rfl⟩ := hr
    obtain ⟨q, rfl⟩ := hs
    exact ⟨p, q, rfl⟩
  have : Algebra.FormallyEtale A F := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  have : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  let : Algebra A K := ((algebraMap F K).comp (algebraMap A F)).toAlgebra
  have : IsScalarTower A F K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq fun r => by
    change _ = algebraMap F K (algebraMap A F (algebraMap k A r))
    rw [← IsScalarTower.algebraMap_apply k A F, ← IsScalarTower.algebraMap_apply k F K]
  have : Algebra.FormallyEtale A K := Algebra.FormallyEtale.comp A F K
  refine ⟨((KaehlerDifferential.mvPolynomialBasis k (Fin d)).baseChange K).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A K), fun j => ?_⟩
  have hb0 : KaehlerDifferential.mvPolynomialBasis k (Fin d) j = D k A (MvPolynomial.X j) :=
    (KaehlerDifferential.mvPolynomialBasis k (Fin d)).repr.injective (by
      rw [Module.Basis.repr_self, KaehlerDifferential.mvPolynomialBasis_repr_D_X])
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb0,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, KaehlerDifferential.mapBaseChange_tmul,
    one_smul, KaehlerDifferential.map_D]
  change D k K (algebraMap F K (MvPolynomial.aeval t (MvPolynomial.X j))) = _
  rw [MvPolynomial.aeval_X]

theorem IsFinCover.exists_isTop (h : IsFinCover k K x) : ∃ τ : DR k K →ₗ[K] K, IsTop k K x τ := by
  obtain ⟨b, hb⟩ := h.exists_basis
  have hne : ∀ j : Fin d, algebraMap F K (x j.succ / x 0) ≠ 0 := fun j =>
    (map_ne_zero _).mpr (div_ne_zero (h.pd.ne _) (h.pd.ne _))
  let b' := b.unitsSMul fun j => (Units.mk0 _ (hne j))⁻¹
  have hb' : ∀ j, b' j =
      (algebraMap F K (x j.succ / x 0))⁻¹ • D k K (algebraMap F K (x j.succ / x 0)) := by
    intro j
    simp [b', Module.Basis.unitsSMul_apply, Units.smul_def, hb]
  let φ : ⋀[K]^d Ω[K⁄k] →ₗ[K] K := exteriorPower.alternatingMapLinearEquiv b'.det
  let τ : DR k K →ₗ[K] K := φ ∘ₗ DirectSum.component K ℕ (fun i => ⋀[K]^i Ω[K⁄k]) d ∘ₗ
    (DirectSum.decomposeLinearEquiv (fun i : ℕ => ⋀[K]^i Ω[K⁄k])).toLinearMap
  have key : ∀ y : DR k K, τ y = φ (DirectSum.decompose (fun i : ℕ => ⋀[K]^i Ω[K⁄k]) y d) :=
    fun y => rfl
  refine ⟨τ, ?_⟩
  unfold IsTop
  constructor
  · have hv : vol0 k K x = ExteriorAlgebra.ιMulti K d b' := by
      unfold vol0
      congr 1
      funext j
      exact (hb' j).symm
    rw [key, hv, ← exteriorPower.ιMulti_apply_coe, DirectSum.decompose_coe, DirectSum.of_eq_same,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Module.Basis.det_self]
  · intro q hq y hy
    have hz : DirectSum.decompose (fun i : ℕ => ⋀[K]^i Ω[K⁄k]) y d = 0 := by
      ext1
      exact DirectSum.decompose_of_mem_ne _ hy hq
    rw [key, hz, map_zero]

theorem IsFinCover.dlogRatioVolumeForm_ne_zero (h : IsFinCover k K x) : vol0 k K x ≠ 0 := by
  obtain ⟨τ, hτ⟩ := h.exists_isTop
  unfold IsTop at hτ
  intro h0
  have h1 := hτ.1
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

end API

end GlobalTheory.PD
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.GalV

variable (l : ℕ) [Fact l.Prime]

abbrev Htot (E : Spc) : Type 1 := DirectSum ℤ fun n : ℤ => HQ l E n 0

def pullTot {E E' : Spc} (f : E ⟶ E') : Htot l E' →ₗ[ℚ_[l]] Htot l E :=
  DirectSum.lmap fun n => pullHQ l f n 0

theorem pullTot_id (E : Spc) : pullTot l (𝟙 E) = LinearMap.id := by
  simp only [pullTot, pullHQ, pullHl_id, LinearMap.baseChange_id]
  exact DirectSum.lmap_id

theorem pullTot_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') :
    pullTot l (f ≫ g) = pullTot l f ∘ₗ pullTot l g := by
  simp only [pullTot, pullHQ, pullHl_comp, LinearMap.baseChange_comp]
  exact DirectSum.lmap_comp _ _

def galTot {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    (Ω ≃ₐ[k] Ω) → Htot l (sch.obj (GlobalTheory.Et.geom Ω p)) →ₗ[ℚ_[l]] Htot l (sch.obj (GlobalTheory.Et.geom Ω p)) :=
  fun σ => pullTot l (sch.map (GlobalTheory.Et.galMap Ω p σ))

private theorem galMap_one' {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) : GlobalTheory.Et.galMap Ω p (1 : Ω ≃ₐ[k] Ω) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [GlobalTheory.Et.galMap_fst, Category.id_comp]
  · rw [GlobalTheory.Et.galMap_snd, Category.id_comp]
    have h1 : CommRingCat.ofHom ((1 : Ω ≃ₐ[k] Ω) : Ω →+* Ω) = 𝟙 _ := by
      ext x; rfl
    rw [h1, Spec.map_id, Category.comp_id]

theorem galTot_one {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    galTot l Ω p 1 = LinearMap.id := by
  simp only [galTot]
  rw [galMap_one', CategoryTheory.Functor.map_id, pullTot_id]

private theorem galMap_mul' {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) (σ τ : Ω ≃ₐ[k] Ω) :
    GlobalTheory.Et.galMap Ω p (σ * τ) = GlobalTheory.Et.galMap Ω p σ ≫ GlobalTheory.Et.galMap Ω p τ := by
  apply pullback.hom_ext
  · rw [GlobalTheory.Et.galMap_fst, Category.assoc, GlobalTheory.Et.galMap_fst, GlobalTheory.Et.galMap_fst]
  · have h2 : CommRingCat.ofHom ((σ * τ : Ω ≃ₐ[k] Ω) : Ω →+* Ω) =
        CommRingCat.ofHom (τ : Ω →+* Ω) ≫ CommRingCat.ofHom (σ : Ω →+* Ω) := by
      ext x; rfl
    rw [GlobalTheory.Et.galMap_snd, Category.assoc, GlobalTheory.Et.galMap_snd, GlobalTheory.Et.galMap_snd_assoc, h2, Spec.map_comp]

theorem galTot_mul {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))
    (σ τ : Ω ≃ₐ[k] Ω) : galTot l Ω p (σ * τ) = galTot l Ω p σ ∘ₗ galTot l Ω p τ := by
  simp only [galTot]
  rw [galMap_mul', CategoryTheory.Functor.map_comp, pullTot_comp]

def galTotRep {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    Representation ℚ_[l] (Ω ≃ₐ[k] Ω) (Htot l (sch.obj (GlobalTheory.Et.geom Ω p))) where
  toFun := galTot l Ω p
  map_one' := galTot_one l Ω p
  map_mul' := galTot_mul l Ω p

def Splits {Z Y W : Scheme.{0}} (s : Y ⟶ Z) (c : W ⟶ Z) {J : Type} (σ : J → (W ⟶ Y)) : Prop :=
  ∃ h : ∀ j, σ j ≫ s = c,
    IsIso (Limits.Sigma.desc (fun j => pullback.lift (σ j) (𝟙 W) (by rw [h j, Category.id_comp])) :
      ∐ (fun _ : J => W) ⟶ pullback s c)

def IsGalois {W X : Scheme.{0}} (c : W ⟶ X) (G : Type) [Group G] (a : G → (W ⟶ W)) : Prop :=
  IsFinite c ∧ Etale c ∧ Surjective c ∧ a 1 = 𝟙 W ∧ (∀ g h, a (g * h) = a g ≫ a h) ∧ Splits c c a

def IsCorrOp {Z Y Z' : Scheme.{0}} (s : Y ⟶ Z) (t : Y ⟶ Z') (T : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z)) : Prop :=
  ∃ (W : Scheme.{0}) (c : W ⟶ Z) (G : Type) (_ : Group G) (_ : Finite G) (a : G → (W ⟶ W)) (J : Type) (_ : Fintype J)
    (σ : J → (W ⟶ Y)), IsGalois c G a ∧ Splits s c σ ∧
    ∀ x, pullTot l (sch.map c) (T x) = ∑ j, pullTot l (sch.map (σ j ≫ t)) x

variable {l}

def genEig {H : Type*} [AddCommGroup H] [Module ℚ_[l] H] (L : Type*) [Field L] [Algebra ℚ_[l] L] {J : Type*}
    (T : J → H →ₗ[ℚ_[l]] H) (θ : J → L) : Submodule L (TensorProduct ℚ_[l] L (H)) :=
  ⨅ j, Module.End.maxGenEigenspace ((T j).baseChange L) (θ j)

variable (l)

theorem isGalois_id (X : Scheme.{0}) : IsGalois (𝟙 X) Unit (fun _ => 𝟙 X) := by
  refine ⟨inferInstance, inferInstance, inferInstance, rfl, fun _ _ => (Category.comp_id _).symm,
    fun _ => Category.comp_id _, ?_⟩
  have hd : IsIso (Sigma.desc (fun _ : Unit => 𝟙 X)) :=
    ⟨⟨Sigma.ι (fun _ : Unit => X) (), by ext j; cases j; simp, by simp⟩⟩
  refine (isIso_comp_right_iff _ (pullback.fst (𝟙 X) (𝟙 X))).mp ?_
  convert hd using 1
  ext j
  simp

theorem splits_fold (X : Scheme.{0}) (J : Type) :
    Splits (Sigma.desc fun _ : J => 𝟙 X) (𝟙 X) (Sigma.ι (fun _ : J => X)) := by
  refine ⟨fun _ => by simp, ?_⟩
  refine (isIso_comp_right_iff _ (pullback.fst (Sigma.desc fun _ : J => 𝟙 X) (𝟙 X))).mp ?_
  convert (inferInstance : IsIso (𝟙 (∐ fun _ : J => X))) using 1
  ext j
  simp

theorem isCorrOp_fold {X Z' : Scheme.{0}} {J : Type} [Fintype J] (f : J → (X ⟶ Z')) :
    IsCorrOp l (Sigma.desc fun _ : J => 𝟙 X) (Sigma.desc f) (∑ j, pullTot l (sch.map (f j))) := by
  refine ⟨X, 𝟙 X, Unit, inferInstance, inferInstance, fun _ => 𝟙 X, J, inferInstance, Sigma.ι (fun _ : J => X),
    isGalois_id X, splits_fold X J, fun x => ?_⟩
  rw [CategoryTheory.Functor.map_id, pullTot_id, LinearMap.id_apply, LinearMap.sum_apply]
  simp only [Sigma.ι_comp_desc]

end GlobalTheory.GalV

end
end
