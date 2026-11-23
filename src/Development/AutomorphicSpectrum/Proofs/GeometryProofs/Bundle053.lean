module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle038
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle040
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle039
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Presheaf
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

section
variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ} {Li : Type} [AddCommGroup Li] [Module K Li]

def latOn (D : HTChart A K c p R N (Module.Dual K Li)) (V : Submodule K Li) (t : K) (B : Subring K) : Set Li :=
  {e | e ∈ V ∧ ∀ w ∈ D.om', t * w e ∈ B}

def IsLocIn (A : Type) {K : Type} [CommRing A] [Field K] [Algebra A K] (B : Subring K) : Prop :=
  (∀ a : A, algebraMap A K a ∈ B) ∧
    ∀ b ∈ B, ∃ u a : A, algebraMap A K u ≠ 0 ∧ (algebraMap A K u)⁻¹ ∈ B ∧ algebraMap A K u * b = algebraMap A K a

end
end GlobalTheory.CompanionTheory.Ar.Flat.HTL

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

theorem exists_extend_lin {A K V W : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower A K W]
    (M : Submodule A V) (g : M →ₗ[A] W) : ∃ G : V →ₗ[K] W, ∀ z : M, G z = g z := by
  classical
  obtain ⟨b, hbM, -, hsp, hli⟩ := exists_linearIndepOn_id_extension (K := K) (s := ∅) (t := (M : Set V)) (by simp) (by simp)
  let bb := Basis.extend hli
  let f : V → W := fun x => if h : x ∈ M then g ⟨x, h⟩ else 0
  let G : V →ₗ[K] W := bb.constr K fun i => f i.1
  have hGb : ∀ x ∈ b, G x = f x := fun x hx => by
    have hx' : x ∈ hli.extend (Set.subset_univ b) := hli.subset_extend _ hx
    have := bb.constr_basis K (fun i => f i.1) ⟨x, hx'⟩
    simpa [bb, G, Basis.extend_apply_self] using this
  have hG : ∀ x (hx : x ∈ Submodule.span A b) (h : x ∈ M), G x = g ⟨x, h⟩ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro h
      rw [hGb x hx]
      simp [f, h]
    | zero =>
      intro h
      have : (⟨0, h⟩ : M) = 0 := rfl
      rw [this, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      intro h
      have h1 : x ∈ M := Submodule.span_le.2 hbM hx
      have h2 : y ∈ M := Submodule.span_le.2 hbM hy
      have : (⟨x + y, h⟩ : M) = ⟨x, h1⟩ + ⟨y, h2⟩ := rfl
      rw [map_add (f := _), ihx h1, ihy h2, this, map_add (f := _)]
    | smul a x hx ih =>
      intro h
      have h1 : x ∈ M := Submodule.span_le.2 hbM hx
      have : (⟨a • x, h⟩ : M) = a • ⟨x, h1⟩ := rfl
      rw [this, g.map_smul, ← ih h1, LinearMap.map_smul_of_tower]
  have hden : ∀ v ∈ Submodule.span K b, ∃ a : A, algebraMap A K a ≠ 0 ∧ a • v ∈ Submodule.span A b := by
    intro v hv
    have hinj := IsFractionRing.injective A K
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, by simp, by simpa using Submodule.subset_span hx⟩
    | zero => exact ⟨1, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨a', ha', hy⟩ := hy
      refine ⟨a * a', by rw [map_mul]; exact mul_ne_zero ha ha', ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul r x _ hx =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := A) r
      have hv0 : algebraMap A K v ≠ 0 := (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hv)
      refine ⟨v * a, by rw [map_mul]; exact mul_ne_zero hv0 ha, ?_⟩
      have : (v * a) • (algebraMap A K u / algebraMap A K v) • x = u • a • x := by
        rw [← algebraMap_smul K (v * a), ← algebraMap_smul K u, ← algebraMap_smul K a, smul_smul, smul_smul, map_mul]
        congr 1
        field_simp
      rw [this]
      exact Submodule.smul_mem _ _ hx
  refine ⟨G, fun z => ?_⟩
  obtain ⟨a, ha, haz⟩ := hden z (hsp z.2)
  have h1 := hG _ haz (M.smul_mem a z.2)
  have h2 : (⟨a • (z : V), M.smul_mem a z.2⟩ : M) = a • z := rfl
  rw [h2, g.map_smul, LinearMap.map_smul_of_tower, ← algebraMap_smul K a (G (z : V)), ← algebraMap_smul K a (g z)] at h1
  exact smul_right_injective W ha h1

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ} {Li : Type} [AddCommGroup Li] [Module K Li]
  (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li)

theorem eigProj_dual (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) (w : Module.Dual K Li) :
    eigProj D.ρΩ σ w = w ∘ₗ eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ := by
  ext v
  simp [eigProj, LinearMap.sum_apply, hact]

theorem eigProj_apply (hc : ∀ x, c (c x) = x)
    (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) {e : Li} (he : e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) (w : Module.Dual K Li) :
    eigProj D.ρΩ σ w e = w e := by
  rw [eigProj_dual D ρ hact, LinearMap.comp_apply]
  congr 1
  have h1 : ∀ a : 𝓞 E, ρ (RingOfIntegers.mapRingEquiv c a) e = σ (a : E) • e := fun a => by
    rw [LatBasic.mem_eigSp.1 he]
    simp [hc]
  have h2 : eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ e = e := by
    apply LatBasic.eigProj_of_mem
    rw [LatBasic.mem_eigSp]
    exact fun a => h1 a
  exact h2

theorem exists_vec [IsDomain A] [IsFractionRing A K] (hc : ∀ x, c (c x) = x)
    (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) (g : Module.Dual A (D.omHT σ)) :
    ∃ e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom), ∀ z : D.omHT σ,
      (z : Module.Dual K Li) e = algebraMap A K (g z) := by
  let U : Submodule K (Module.Dual K Li) := Submodule.span K (D.om : Set _)
  haveI : Module.Finite K U := by
    obtain ⟨S, hS⟩ := D.om_lat.fg
    have : U = Submodule.span K (S : Set _) := by
      dsimp [U]
      rw [← hS, Submodule.span_span_of_tower]
    rw [this]
    exact Module.Finite.span_of_finite K S.finite_toSet
  let T := U.map (eigProj D.ρΩ σ)
  haveI : Module.Finite K T := Module.Finite.iff_fg.mpr (Submodule.FG.map (eigProj D.ρΩ σ) (Module.Finite.iff_fg.mp (show Module.Finite K U from inferInstance)))
  obtain ⟨G, hG⟩ := exists_extend_lin (K := K) (D.omHT σ) ((Algebra.linearMap A K) ∘ₗ g)
  let B : Li →ₗ[K] Module.Dual K T := T.subtype.dualMap.comp (Module.Dual.eval K Li)
  have hB : Function.Injective B.flip := by
    intro x y h
    apply Subtype.ext
    ext v
    exact LinearMap.congr_fun h v
  obtain ⟨v, hv⟩ := (LinearMap.flip_injective_iff₂.mp hB) (G.comp T.subtype)
  have hv' : ∀ w ∈ T, w v = G w := by
    intro w hw
    exact LinearMap.congr_fun hv ⟨w, hw⟩
  have hom : D.om' ≤ D.om := by
    rw [HTChart.om', sup_le_iff]
    constructor
    · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr D.h_mem)
    · rintro _ ⟨x, hx, rfl⟩
      exact D.om.smul_mem _ hx
  refine ⟨eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v, ?_, ?_⟩
  · have h := LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v
    rw [LatBasic.mem_eigSp] at h ⊢
    intro a
    have hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
      apply RingOfIntegers.ext
      simp [hc]
    have := h (RingOfIntegers.mapRingEquiv c a)
    simpa [hinv] using this
  · intro z
    obtain ⟨w, hw, hz⟩ := z.2
    have hz' : eigProj D.ρΩ σ w = (z : Module.Dual K Li) := hz
    have he : eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom) := by
      have h := LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v
      rw [LatBasic.mem_eigSp] at h ⊢
      intro a
      have hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
        apply RingOfIntegers.ext
        simp [hc]
      have := h (RingOfIntegers.mapRingEquiv c a)
      simpa [hinv] using this
    rw [← hz', eigProj_apply D ρ hc hact σ he w]
    have h2 : w (eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v) = (eigProj D.ρΩ σ w) v := by
      rw [eigProj_dual D ρ hact, LinearMap.comp_apply]
    have hzT : (z : Module.Dual K Li) ∈ T := by
      rw [← hz']
      exact ⟨w, Submodule.subset_span (hom hw), rfl⟩
    rw [h2, hz', hv' _ hzT, hG z]
    rfl

end Chart

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT.Overlap

theorem omHT_pow_smul_mem : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p R N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω c p R N V), (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}), ∀ x ∈ (Dc s).om, ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).om) → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (x : Fin N → 𝓞 E), ∃ n : ℕ, ∃ w ∈ (Dc t).om, (mseg y s.1 / mseg y t.1) ^ n • ((Dc s).h x - (Dc t).h x) = ((p : Ω) ^ R) • w) → (∀ s t, (Dc s).ρΩ = (Dc t).ρΩ) → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}), ∀ a ∈ chartRing o (mseg y) s.1, ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n * a ∈ chartRing o (mseg y) t.1) → ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω), ∀ x ∈ (Dc s).omHT σ', ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).omHT σ' := by
  intro o _ Ω _ _ K _ J _ y E _ _ c p R N V _ _ Dc hom hh hρ hring s t σ'
  set f : Ω := mseg y s.1 / mseg y t.1 with hf
  have hfA : f ∈ chartRing o (mseg y) t.1 := Algebra.subset_adjoin ⟨s.1, rfl⟩
  have hfMn : ∀ n : ℕ, ∀ z ∈ (Dc t).om', f ^ n • z ∈ (Dc t).om' := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih =>
      intro z hz
      rw [pow_succ', mul_smul]
      exact (Dc t).om'.smul_mem (⟨f, hfA⟩ : chartRing o (mseg y) t.1) (ih z hz)
  let P : Submodule (chartRing o (mseg y) s.1) V :=
    { carrier := {z | ∃ n : ℕ, f ^ n • z ∈ (Dc t).om'}
      add_mem' := by
        rintro a b ⟨n, hn⟩ ⟨m, hm⟩
        refine ⟨n + m, ?_⟩
        rw [smul_add]
        refine add_mem ?_ ?_
        · rw [add_comm, pow_add, mul_smul]; exact hfMn m _ hn
        · rw [pow_add, mul_smul]; exact hfMn n _ hm
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro a z ⟨n, hn⟩
        obtain ⟨m, hm⟩ := hring s t (a : Ω) a.2
        refine ⟨n + m, ?_⟩
        have e1 : f ^ (n + m) • (a • z) = (⟨f ^ m * a, hm⟩ : chartRing o (mseg y) t.1) • (f ^ n • z) := by
          show f ^ (n + m) • ((a : Ω) • z) = (f ^ m * a) • (f ^ n • z)
          rw [smul_smul, smul_smul]; congr 1; ring
        rw [e1]; exact (Dc t).om'.smul_mem _ hn }
  have hle : (Dc s).om' ≤ P := by
    unfold HTChart.om'
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨δ, rfl⟩
      obtain ⟨n, w, hw, he⟩ := hh s t δ
      refine ⟨n, ?_⟩
      have e2 : f ^ n • (Dc s).h δ = f ^ n • (Dc t).h δ + ((p : Ω) ^ R) • w := by
        rw [← he, smul_sub]; abel
      rw [e2]
      refine add_mem (hfMn n _ ?_) ?_
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨δ, rfl⟩)
      · refine Submodule.mem_sup_right ⟨w, hw, ?_⟩
        simp [Subalgebra.smul_def]
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨n, hn⟩ := hom s t u hu
      refine ⟨n, ?_⟩
      refine Submodule.mem_sup_right ⟨f ^ n • u, hn, ?_⟩
      simp [Subalgebra.smul_def, smul_comm ((p : Ω) ^ R) (f ^ n) u]
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨n, hn⟩ := hle hz
  refine ⟨n, ⟨f ^ n • z, hn, ?_⟩⟩
  show eigProj (Dc t).ρΩ σ' (f ^ n • z) = f ^ n • eigProj (Dc s).ρΩ σ' z
  rw [hρ s t, map_smul]

end GlobalTheory.CompanionTheory.Ar.HT.Overlap
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.lie_model_complex_linear_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (t' : SAB H (Sp R)) (h : Sp R ⟶ X) (m : SABMap t' t h) (g : ℕ) (M : LieModel t'.G (𝟙 (Sp R)) (Fin g → R)) (ψ : R →+* ℂ) (Vz : Type) [AddCommGroup Vz] [Module ℂ Vz] (MR : LieModel t.G (spMap ψ ≫ h) Vz), ∃ Θ : (Fin g → ℂ) →ₗ[ℂ] Vz, ∀ x : Fin g → R, (MR.pt (Θ (fun e => ψ (x e)))).left = spMap (dualMap ψ) ≫ (M.pt x).left ≫ m.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FrameFibre.exists_linear_fibre | exact GlobalTheory.CompanionTheory.Ar.FrameFibre.exists_linear_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.FrameFibre.exists_linear_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.abelian_map_tangent_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] (i : Sp A ⟶ X) (N : ℕ) (v : Fin N → (epsAt i ⟶ t.G)) (R : Type) [CommRing R] (t' : SAB H (Sp R)) (θ : A →+* R) (m : SABMap t' t (spMap θ ≫ i)) (g : ℕ) (M : LieModel t'.G (𝟙 (Sp R)) (Fin g → R)), (∀ k, IsTanAt t.G i (v k)) → ∃ x : Fin N → Fin g → R, ∀ k, (M.pt (x k)).left ≫ m.φ = spMap (dualMap θ) ≫ (v k).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PeriodCoord.exists_coords | exact GlobalTheory.CompanionTheory.Ar.PeriodCoord.exists_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.PeriodCoord.exists_coords <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hermitian_norm_section_value : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [Nonempty K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (A : HermLine J) (c₀ : Ω) (C : ℝ) (g h : MRing J) (dg dh : K → ℕ), IsCptGen ξ → CoordsAt ξ y z w → (∀ (cc : (k : K) → J k) (u : ℂ), (∀ k, w ⟨k, cc k⟩ ≠ 0) → ValAt ξ z (c₀ / ∏ k, y ⟨k, cc k⟩ ^ A.a k) u → ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = C * A.h w) → IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → evC w h ≠ 0 → ‖evC w g‖ = C * A.h w * ‖evC w h‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.EvalPt.norm_evC_of_forms | exact GlobalTheory.CompanionTheory.Ar.Flat.EvalPt.norm_evC_of_forms | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.EvalPt.norm_evC_of_forms <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartPoint

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

abbrev chartRing {κ : Type} (x : κ → Ω) (c : κ) : Subalgebra ℤ Ω :=
  Algebra.adjoin ℤ (Set.range fun j => x j / x c)

theorem stalk_value (hg : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R] (p : Cpt ξ) (φ : regAt ξ p →+* R)
    (z : Spec (CommRingCat.of R) ⟶ X) (hzc : centre z = p.1) (hv : ∀ a : regAt ξ p, ValAt ξ z (a : Ω) (φ a))
    (h : genPt ξ ⤳ centre z) (s : X.presheaf.stalk (centre z)) :
    ∃ hm : genMap ξ ⟨centre z, h⟩ s ∈ regAt ξ p,
      (Scheme.stalkClosedPointTo z).hom s = φ ⟨genMap ξ ⟨centre z, h⟩ s, hm⟩ := by
  obtain ⟨pp, hpp⟩ := p
  dsimp only at hzc
  subst hzc
  refine ⟨⟨s, rfl⟩, ?_⟩
  obtain ⟨h', s', e1, e2⟩ := hv ⟨genMap ξ ⟨centre z, h⟩ s, ⟨s, rfl⟩⟩
  have e3 : s' = s := hg.inj ⟨centre z, h⟩ e1
  subst e3
  exact e2


set_option backward.isDefEq.respectTransparency false in
theorem spec_square {F : Type} [Field F] (θ : Ω →+* F) {A : Subring F} [IsLocalRing A]
    (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z)
    (hs : ∀ s : X.presheaf.stalk (centre z),
      (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s)) :
    Spec.map (CommRingCat.ofHom A.subtype) ≫ z = Spec.map (CommRingCat.ofHom θ) ≫ ξ := by
  have e : A.subtype.comp (Scheme.stalkClosedPointTo z).hom = θ.comp (genMap ξ ⟨centre z, h⟩) := RingHom.ext hs
  have e1 := LieTangent.spec_centre z
  have e2 := LieTangent.spec_genMap ξ ⟨centre z, h⟩
  calc Spec.map (CommRingCat.ofHom A.subtype) ≫ z
      = Spec.map (CommRingCat.ofHom A.subtype) ≫
          (Spec.map (CommRingCat.ofHom (R := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom) ≫
            X.fromSpecStalk (centre z)) := by rw [e1]
    _ = Spec.map (CommRingCat.ofHom θ) ≫ (Spec.map (CommRingCat.ofHom (genMap ξ ⟨centre z, h⟩)) ≫
            X.fromSpecStalk (centre z)) := by
        rw [← Category.assoc, ← Category.assoc, LieTangent.spec_comp, LieTangent.spec_comp, e]
    _ = Spec.map (CommRingCat.ofHom θ) ≫ ξ := by
        exact congrArg (_ ≫ ·) e2

theorem point_of_local_subring : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ (F : Type) [Field F] (θ : Ω →+* F) (A : Subring F) [IsLocalRing A], (∀ j, θ (x j / x c) ∈ A) → ∃ (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z), InChart ξ x c ⟨centre z, h⟩ ∧ (∀ s : X.presheaf.stalk (centre z), (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s)) ∧ Spec.map (CommRingCat.ofHom A.subtype) ≫ z = Spec.map (CommRingCat.ofHom θ) ≫ ξ := by
  intro X Ω _ ξ κ x c hT hc F _ θ A _ hA
  have hC : ∀ s ∈ chartRing x c, θ s ∈ A := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      exact hA j
    | algebraMap r =>
      have : θ (algebraMap ℤ Ω r) = (r : F) := by simp
      rw [this]
      exact intCast_mem A r
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let θC : chartRing x c →+* A :=
    (θ.comp (chartRing x c).val.toRingHom).codRestrict A (fun s => hC s s.2)
  obtain ⟨p, ⟨hpc, hpu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ κ x hT c hc
    (Ideal.comap θC (IsLocalRing.maximalIdeal A)) inferInstance
  have hunit : ∀ s (hs : s ∈ chartRing x c), unitAt ξ p s ↔ IsUnit (⟨θ s, hC s hs⟩ : A) := by
    intro s hs
    rw [← hpu ⟨s, hs⟩, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    rfl
  have hreg : ∀ a ∈ regAt ξ p, θ a ∈ A := by
    intro a ha
    obtain ⟨s, hs, hsu, hsa⟩ := (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x hT c p hpc a).1 ha
    obtain ⟨u, hu⟩ := (hunit s hs).1 hsu
    have h1 : (((u⁻¹ : Aˣ) : A) : F) * θ s = 1 := by
      have h2 := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at h2
      exact h2
    have h3 : θ a = (((u⁻¹ : Aˣ) : A) : F) * θ (s * a) := by
      rw [map_mul, ← mul_assoc, h1, one_mul]
    rw [h3]
    exact mul_mem ((u⁻¹ : Aˣ) : A).2 (hC _ hsa)
  let φ : regAt ξ p →+* A := (θ.comp (regAt ξ p).subtype).codRestrict A (fun a => hreg a a.2)
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨s, hs, hsu, hsa⟩ := (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x hT c p hpc a).1 a.2
    have hua : IsUnit (⟨θ (s * a), hC _ hsa⟩ : A) := by
      have h1 : (⟨θ (s * a), hC _ hsa⟩ : A) = ⟨θ s, hC s hs⟩ * φ a :=
        Subtype.ext (map_mul θ s a)
      rw [h1]
      exact ((hunit s hs).1 hsu).mul ha
    obtain ⟨h0, -, hi⟩ := (hunit _ hsa).2 hua
    have hs0 : s ≠ 0 := left_ne_zero_of_mul h0
    have ha0 : (a : Ω) ≠ 0 := right_ne_zero_of_mul h0
    have hinv : (a : Ω)⁻¹ ∈ regAt ξ p := by
      have h1 : (a : Ω)⁻¹ = s * (s * a)⁻¹ := by field_simp
      rw [h1]
      exact mul_mem hsu.2.1 hi
    exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ ha0))
  obtain ⟨z, ⟨hzc, hzv⟩, -⟩ := GlobalTheory.T.existsUnique_centre_local_hom X Ω ξ hT.gen p A φ hloc
  have h : genPt ξ ⤳ centre z := by rw [hzc]; exact p.2
  have hp : (⟨centre z, h⟩ : Cpt ξ) = p := Subtype.ext hzc
  have hs : ∀ s : X.presheaf.stalk (centre z),
      (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s) := by
    intro s
    obtain ⟨hm, e⟩ := stalk_value hT.gen p φ z hzc hzv h s
    rw [e]
    rfl
  exact ⟨z, h, by rw [hp]; exact hpc, hs, spec_square θ z h hs⟩

end GlobalTheory.CompanionTheory.Ar.ChartPoint
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.hodge_tate_functional_endomorphism : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (a : G ⟶ G) [IsMonHom a] (α : T →* T) (A : L →ₗ[R] L), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) → M.IsDiffOf a A → ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N (χ.comp α) (w ∘ₗ A) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.hodgeTate_endo | exact GlobalTheory.CompanionTheory.Ar.BT.hodgeTate_endo | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.hodgeTate_endo <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.hodge_tate_functional_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ χ' : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N χ' w' → Γ.IsHT i M N (χ * χ') (w + w') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.isHT_mul_add | exact GlobalTheory.CompanionTheory.Ar.BT.isHT_mul_add | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.isHT_mul_add <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.function_field_ratio_generators : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), h ≠ 0 ∧ a = g / h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin | exact GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.hodge_tate_functional_unique_mod_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → (N : R) ≠ 0 → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → (Γ.IsHT i M N χ w' ↔ ∃ u : Module.Dual R L, w' = w + N • u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.HT.isHT_iff | exact GlobalTheory.CompanionTheory.Ar.BT.HT.isHT_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.HT.isHT_iff <;> assumption)
end
