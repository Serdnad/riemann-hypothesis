module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ArithDegree
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle084
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import GroundTheory.FunctionField.PlaceDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle030
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open NumberField TensorProduct Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Adapted

section Field

variable {k V O : Type} [Field k] [AddCommGroup V] [Module k V] [CommRing O]

theorem eigSp_apply {ρ : O →+* Module.End k V} {σ : O →+* k} {x : V} (hx : x ∈ eigSp ρ σ) (a : O) :
    ρ a x = σ a • x := by
  have h := (Submodule.mem_iInf _).1 hx a
  rw [LinearMap.mem_ker] at h
  simpa [sub_eq_zero] using h

theorem iSup_eigSp_stable (ρ : O →+* Module.End k V) (T : Set (O →+* k)) (a : O) {x : V}
    (hx : x ∈ ⨆ τ ∈ T, eigSp ρ τ) : ρ a x ∈ ⨆ τ ∈ T, eigSp ρ τ := by
  have hle : (⨆ τ ∈ T, eigSp ρ τ) ≤ (⨆ τ ∈ T, eigSp ρ τ).comap (ρ a) := by
    refine iSup₂_le fun τ hτ y hy => ?_
    rw [Submodule.mem_comap, eigSp_apply hy a]
    exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem τ (Submodule.mem_iSup_of_mem hτ hy))
  exact hle hx

theorem eq_zero_of_mem_finset (ρ : O →+* Module.End k V) (σ : O →+* k)
    (t : Finset {τ : O →+* k // τ ≠ σ}) :
    ∀ x ∈ eigSp ρ σ, x ∈ (⨆ i ∈ t, eigSp ρ i.1) → x = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro x _ h
    simpa using h
  | insert τ t _ ih =>
    intro x hx hxs
    rw [Finset.iSup_insert, Submodule.mem_sup] at hxs
    obtain ⟨y, hy, z, hz, hyz⟩ := hxs
    obtain ⟨a, ha⟩ : ∃ a, σ a ≠ τ.1 a := by
      by_contra h
      push_neg at h
      exact τ.2 (RingHom.ext fun a => (h a).symm)
    have hzs : ∀ b : O, ρ b z ∈ ⨆ i ∈ t, eigSp ρ i.1 := by
      intro b
      have hle : (⨆ i ∈ t, eigSp ρ i.1) ≤ (⨆ i ∈ t, eigSp ρ i.1).comap (ρ b) := by
        refine iSup₂_le fun i hi u hu => ?_
        rw [Submodule.mem_comap, eigSp_apply hu b]
        exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi hu))
      exact hle hz
    have hkey : (σ a - τ.1 a) • x = ρ a z - τ.1 a • z := by
      have e1 := eigSp_apply hx a
      have e2 := eigSp_apply hy a
      rw [← hyz, map_add (f := _), e2] at e1
      have e3 : ρ a z = σ a • (y + z) - τ.1 a • y := by rw [← e1]; abel
      rw [e3, ← hyz, sub_smul]
      simp only [smul_add]
      abel
    have hmem : (σ a - τ.1 a) • x ∈ ⨆ i ∈ t, eigSp ρ i.1 := by
      rw [hkey]
      exact Submodule.sub_mem _ (hzs a) (Submodule.smul_mem _ _ hz)
    have h0 := ih _ (Submodule.smul_mem _ _ hx) hmem
    exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 ha)

theorem eq_zero_of_mem_iSup (ρ : O →+* Module.End k V) (σ : O →+* k) {x : V} (hx : x ∈ eigSp ρ σ)
    (hS : x ∈ ⨆ τ ∈ {τ : O →+* k | τ ≠ σ}, eigSp ρ τ) : x = 0 := by
  have h : (⨆ τ ∈ {τ : O →+* k | τ ≠ σ}, eigSp ρ τ) = ⨆ i : {τ : O →+* k // τ ≠ σ}, eigSp ρ i.1 := by
    rw [iSup_subtype']
    rfl
  rw [h, Submodule.mem_iSup_iff_exists_finset] at hS
  obtain ⟨t, ht⟩ := hS
  exact eq_zero_of_mem_finset ρ σ t x hx ht

theorem eigComp_spec {ρ : O →+* Module.End k V} {σ : O →+* k} {x : V} (h0 : eigComp ρ σ x ≠ 0) :
    eigComp ρ σ x ∈ eigSp ρ σ ∧ x - eigComp ρ σ x ∈ ⨆ τ ∈ {τ : O →+* k | τ ≠ σ}, eigSp ρ τ := by
  by_cases h : ∃ p ∈ eigSp ρ σ, x - p ∈ ⨆ σ' ∈ {σ' : O →+* k | σ' ≠ σ}, eigSp ρ σ'
  · have e : eigComp ρ σ x = h.choose := by
      unfold eigComp
      rw [dite_eq_left h]
    rw [e]
    exact h.choose_spec
  · exact absurd (by unfold eigComp; rw [dite_eq_right h]) h0

end Field

section Main

variable {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]

theorem linearIndependent_f (A : LinPt E L Ψ V) (s : Ψ ⊕ Ψ) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ)
    (hO : IsOFamily A.ρ A.I v) (hA : A.IsAdapted s v q) (hq : ∀ i, (q i : V) ∈ A.eig s) :
    LinearIndependent (𝓞 L) fun c => A.f (q c) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg c
  set S : Submodule L V := ⨆ τ ∈ {τ : 𝓞 E →+* L | τ ≠ A.σ s}, eigSp A.ρ τ with hSdef
  set p : Fin r → V := fun i => eigComp A.ρ (A.σ s) (v i) with hpdef
  have hfam_l : ∀ i : Fin r, A.fam s v q (Fin.castAdd k i) = p i := by
    intro i
    simp [LinPt.fam, hpdef]
  have hfam_r : ∀ c : Fin k, A.fam s v q (Fin.natAdd r c) = (q c : V) := by
    intro c
    simp [LinPt.fam]
  have hp : ∀ i, p i ∈ eigSp A.ρ (A.σ s) ∧ v i - p i ∈ S := by
    intro i
    refine eigComp_spec ?_
    have := hA.1.ne_zero (Fin.castAdd k i)
    rwa [hfam_l] at this
  set M : Submodule L V := Submodule.span L (Set.range p) ⊔ S with hMdef
  have hT : ∀ (a : 𝓞 E) (i : Fin r), A.ρ a (v i) ∈ M := by
    intro a i
    have e : A.ρ a (v i) = A.σ s a • p i + A.ρ a (v i - p i) := by
      rw [map_sub, eigSp_apply (hp i).1 a]
      abel
    rw [e]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_sup_left
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    · exact Submodule.mem_sup_right (iSup_eigSp_stable A.ρ _ a (hp i).2)
  have hoS : oSpan A.ρ v ≤ M.toAddSubgroup := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨a, i, rfl⟩
    exact hT a i
  have hI : ∀ x ∈ A.I, x ∈ M := by
    intro x hx
    obtain ⟨n, hn, -, hnx⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hO.2.2 hx
    have h1 : n • x ∈ M := hoS hnx.1
    have hn0 : (n : L) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have h2 : x = (n : L)⁻¹ • (n • x) := by
      rw [← Nat.cast_smul_eq_nsmul L, smul_smul, inv_mul_cancel₀ hn0, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  set w : A.Λ := ∑ c, g c • q c with hw
  have hwV : (w : V) = ∑ c, g c • (q c : V) := by
    simp [hw]
  have hfw : A.f w = 0 := by

    simpa [hw, map_sum] using hg
  have hwI : (w : V) ∈ Submodule.span (𝓞 L) (A.I : Set V) := (A.ker w).1 hfw
  have hwe : (w : V) ∈ eigSp A.ρ (A.σ s) := by
    have : (w : V) ∈ (eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L) := by
      rw [hwV]
      exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hq c).2
    exact this
  have hwM : (w : V) ∈ M := by
    have hle : Submodule.span (𝓞 L) (A.I : Set V) ≤ M.restrictScalars (𝓞 L) :=
      Submodule.span_le.2 fun x hx => hI x hx
    exact hle hwI
  obtain ⟨u, hu, t, ht, hut⟩ := Submodule.mem_sup.1 hwM
  have hue : u ∈ eigSp A.ρ (A.σ s) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨i, rfl⟩
    exact (hp i).1
  have ht0 : t = 0 := by
    refine eq_zero_of_mem_iSup A.ρ (A.σ s) ?_ ht
    have : t = (w : V) - u := by rw [← hut]; abel
    rw [this]
    exact Submodule.sub_mem _ hwe hue
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hu
  have hzero : ∑ j, (Fin.append (fun i => - b i) (fun c => algebraMap (𝓞 L) L (g c)) j) • A.fam s v q j = 0 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, hfam_l, hfam_r, neg_smul, algebraMap_smul,
      Finset.sum_neg_distrib]
    rw [hb, ← hwV, ← hut, ht0]
    simp
  have := Fintype.linearIndependent_iff.1 hA.1 _ hzero (Fin.natAdd r c)
  rw [Fin.append_right] at this
  exact RingOfIntegers.coe_injective (by simpa using this)

end Main

end GlobalTheory.CompanionTheory.Ar.Cusp.Adapted

namespace GlobalTheory.CompanionTheory.Ar.Cusp


open scoped ComplexOrder in
theorem gramDet_pos_of_adapted : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] (V : Type)
    [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (s : Ψ ⊕ Ψ) (r k : ℕ)
    (v : Fin r → V) (q : Fin k → A.Λ), IsOFamily A.ρ A.I v → A.IsAdapted s v q → (∀ i, (q i : V) ∈ A.eig s) →
    ∀ e : L →+* ℂ, 0 < A.gramDet e q := by
  intro E L Ψ _ _ _ _ V _ _ _ _ A s r k v q hO hA hq e
  have hli := Adapted.linearIndependent_f A s v q hO hA hq
  have hG : (Matrix.gram ℂ fun i ↦ fibreVec A.Bq.metric e (A.f (q i))) =
      Matrix.of fun i j ↦ (A.Bq.metric.form e).inner
        ((1 : ComplexAt e) ⊗ₜ[𝓞 L] A.f (q i)) ((1 : ComplexAt e) ⊗ₜ[𝓞 L] A.f (q j)) := by
    ext i j
    rfl
  have hp := (Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec A.Bq.metric e hli)).det_pos
  rw [hG] at hp
  exact (Complex.lt_def.1 hp).1

end GlobalTheory.CompanionTheory.Ar.Cusp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

section Ip

variable (R : RiemLat E g Λ)

theorem ip_add_right (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_smul_right (c : ℂ) (x y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem ip_conj (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip x y) = R.ip y x := by
  show star (y ⬝ᵥ R.Hm *ᵥ star x) = x ⬝ᵥ R.Hm *ᵥ star y
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

def ipL (x : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun := R.ip x
  map_add' := ip_add_right R x
  map_smul' c y := ip_smul_right R c x y

theorem ip_add_left (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  rw [← ip_conj R y, ip_add_right, map_add (f := _), ip_conj, ip_conj]

theorem ip_smul_left (c : ℂ) (x y : Fin g → ℂ) : R.ip (c • x) y = starRingEnd ℂ c * R.ip x y := by
  rw [← ip_conj R y, ip_smul_right, map_mul, ip_conj]

end Ip

section Eig

variable (R : RiemLat E g Λ)

theorem ip_sum_right {A : Type} (t : Finset A) (f : A → Fin g → ℂ) (x : Fin g → ℂ) :
    R.ip x (∑ i ∈ t, f i) = ∑ i ∈ t, R.ip x (f i) := map_sum (ipL R x) f t

theorem ip_sum_left {A : Type} (t : Finset A) (f : A → Fin g → ℂ) (y : Fin g → ℂ) :
    R.ip (∑ i ∈ t, f i) y = ∑ i ∈ t, R.ip (f i) y := by

  rw [← ip_conj R y, ip_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => ip_conj R y (f i)


omit [IsCMField E] in
theorem comp_ne {s s' : E →+* ℂ} (h : s ≠ s') :
    s.comp (algebraMap (𝓞 E) E) ≠ s'.comp (algebraMap (𝓞 E) E) :=
  fun e => h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e)


omit [IsCMField E] in
theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def extEmb (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (emb_injective s)

omit [IsCMField E] in
theorem extEmb_apply (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : extEmb s (algebraMap (𝓞 E) E a) = s a :=
  IsFractionRing.lift_algebraMap (emb_injective s) a

omit [IsCMField E] in
theorem extEmb_comp (s : 𝓞 E →+* ℂ) : (extEmb s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext (extEmb_apply s)


end Eig

section Family

variable {K : Type} {J : K → Type} {Ψ : Type}



variable {T : Set ((Σ k, J k) → ℂ)} {R : ((Σ k, J k) → ℂ) → RiemLat E g Λ} {w : (Σ k, J k) → ℂ}

end Family

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.Lin
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Compare

theorem eq_val_mul : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W U U' : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T T' : Ω) (d d' : ℕ) (B : Set (Fin d → ℂ)) (B' : Set (Fin d' → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (Y' : (Fin d' → ℂ) → (Sp ℂ ⟶ X)) (H : (Fin d → ℂ) → ℂ) (H' : (Fin d' → ℂ) → ℂ) (b₁ : Fin d → ℂ) (b₂ : Fin d' → ℂ) (r : ℂ), IsCptGen ξ → HChart s ξ W U F T B Y H → HChart s ξ W U' F T' B' Y' H' → (∀ (q : X) (hq : genPt ξ ⤳ q), q ∈ U → q ∈ W → unitAt ξ ⟨q, hq⟩ T) → (∀ (q : X) (hq : genPt ξ ⤳ q), q ∈ U' → q ∈ W → unitAt ξ ⟨q, hq⟩ T') → b₁ ∈ B → b₂ ∈ B' → Y b₁ = Y' b₂ → ValAt ξ (Y b₁) (T' / T) r → H b₁ = r * H' b₂ := by
  intro X s Ω _ ξ W U U' F T T' d d' B B' Y Y' H H' b₁ b₂ r hξ hC hC' hT hT' hb₁ hb₂ hY hval
  obtain ⟨hsp, st, hst1, -⟩ := id hval
  have hreg : T' / T ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.centre (Y b₁), hsp⟩ := by
    unfold GlobalTheory.CompanionTheory.Ar.regAt
    exact RingHom.mem_range.mpr ⟨st, hst1⟩
  obtain ⟨N, hqN, v, -, hv⟩ := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.exists_section hsp hreg ⊤ (by simp)
  have hgN : GlobalTheory.CompanionTheory.Ar.genPt ξ ∈ N := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.genPt_mem hsp hqN
  have hvg : GlobalTheory.CompanionTheory.Ar.Flat.GagaC.genV ξ N hgN v = T' / T := by
    rw [← GlobalTheory.CompanionTheory.Ar.Flat.GagaC.genMap_germ N hsp hqN hgN v]
    exact hv
  have hvalg : ∀ b ∈ B, ∀ hbN : GlobalTheory.CompanionTheory.Ar.centre (Y b) ∈ N,
      GlobalTheory.CompanionTheory.Ar.ValAt ξ (Y b) (T' / T) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v) := by
    intro b hb hbN
    apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.of_section hbN (hC.cpt b hb)
    rw [GlobalTheory.CompanionTheory.Ar.Flat.GagaC.genMap_germ N (hC.cpt b hb) hbN hgN v]
    exact hvg
  have hr : ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b₁) N v = r :=
    GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.unique hξ (hvalg b₁ hb₁ hqN) hval
  obtain ⟨ε, κ, hε, -, hκd, hκ1, hκ⟩ :=
    hC'.chart.factor d B Y hC.chart.isOpen hC.chart.hol hC.chart.isOver b₁ hb₁ b₂ hb₂ hY
  obtain ⟨hOopen, hgd⟩ := hC.chart.hol N v
  obtain ⟨S, hSdef⟩ : ∃ S : Set (Fin d → ℂ),
      S = {b | b ∈ B ∧ ⊤ ≤ (TopologicalSpace.Opens.map (Y b).base).obj N} := ⟨_, rfl⟩
  have hmemS : ∀ b, b ∈ S ↔ b ∈ B ∧ GlobalTheory.CompanionTheory.Ar.centre (Y b) ∈ N := by
    intro b
    rw [hSdef, Set.mem_ofPred_eq, GlobalTheory.CompanionTheory.Ar.Flat.GagaC.top_le_iff_centre]
  have hSo : IsOpen S := by
    rw [hSdef]
    exact hOopen
  have hSg : DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v) S := by
    rw [hSdef]
    exact hgd
  have hOo : IsOpen (S ∩ Metric.ball b₁ ε) := hSo.inter Metric.isOpen_ball
  have h1 : ContinuousOn H (S ∩ Metric.ball b₁ ε) :=
    (hC.hol.mono fun b (hb : b ∈ S ∩ Metric.ball b₁ ε) => ((hmemS b).mp hb.1).1).continuousOn
  have h2 : ContinuousOn (fun b => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v) (S ∩ Metric.ball b₁ ε) :=
    (hSg.mono fun b (hb : b ∈ S ∩ Metric.ball b₁ ε) => hb.1).continuousOn
  have h3 : ContinuousOn (fun b => H' (κ b)) (S ∩ Metric.ball b₁ ε) := by
    have hc : DifferentiableOn ℂ (H' ∘ κ) (Metric.ball b₁ ε) :=
      hC'.hol.comp hκd (fun b hb => (hκ b hb).1)
    exact (hc.mono fun b (hb : b ∈ S ∩ Metric.ball b₁ ε) => hb.2).continuousOn
  have hcont : ContinuousOn (fun b => H b - ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v * H' (κ b))
      (S ∩ Metric.ball b₁ ε) := h1.sub (h2.mul h3)
  have hzero : ∀ b ∈ S ∩ Metric.ball b₁ ε, GlobalTheory.CompanionTheory.Ar.centre (Y b) ∈ W →
      H b - ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v * H' (κ b) = 0 := by
    intro b hbO hbW
    obtain ⟨hbB, hbN⟩ := (hmemS b).mp hbO.1
    obtain ⟨hκB, hYκ⟩ := hκ b hbO.2
    have hcb := hC.cpt b hbB
    have hTu := hT (GlobalTheory.CompanionTheory.Ar.centre (Y b)) hcb (hC.inU b hbB) hbW
    obtain ⟨r₁, hr₁, e₁⟩ := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.exists_ne_zero hξ hcb hTu
    have hcb' := hC'.cpt (κ b) hκB
    have hW' : GlobalTheory.CompanionTheory.Ar.centre (Y' (κ b)) ∈ W := by
      rw [← hYκ]
      exact hbW
    have hT'u := hT' (GlobalTheory.CompanionTheory.Ar.centre (Y' (κ b))) hcb' (hC'.inU (κ b) hκB) hW'
    obtain ⟨r₂, -, e₂⟩ := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.exists_ne_zero hξ hcb' hT'u
    have f₁ := hC.rel b hbB hbW r₁ e₁
    have f₂ := hC'.rel (κ b) hκB hW' r₂ e₂
    have hm := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.mul (hvalg b hbB hbN) e₁
    have hTT : T' / T * T = T' := by
      rw [div_mul_eq_mul_div, mul_div_assoc, div_self hTu.1, _root_.mul_one]
    rw [hTT] at hm
    have e₂' : GlobalTheory.CompanionTheory.Ar.ValAt ξ (Y b) T' r₂ := by
      rw [hYκ]
      exact e₂
    have hu := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.unique hξ hm e₂'
    rw [hYκ] at f₁
    rw [f₁, ← hu] at f₂
    have hH : H b = ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v * H' (κ b) := by
      apply mul_right_cancel₀ hr₁
      rw [f₂]
      ring
    rw [hH, sub_self]
  have hb1O : b₁ ∈ S ∩ Metric.ball b₁ ε := ⟨(hmemS b₁).mpr ⟨hb₁, hqN⟩, Metric.mem_ball_self hε⟩
  have hφ : H b₁ - ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b₁) N v * H' (κ b₁) = 0 := by
    by_contra hne
    have hopen := hcont.isOpen_inter_preimage hOo (isOpen_compl_singleton (x := (0 : ℂ)))
    obtain ⟨b, hb, hbW⟩ := hC.dense _ hopen (fun b hb => ((hmemS b).mp hb.1.1).1) ⟨b₁, hb1O, hne⟩
    exact hb.2 (hzero b hb.1 hbW)
  rw [hr, hκ1] at hφ
  exact sub_eq_zero.mp hφ

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Compare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

namespace GlobalTheory.CompanionTheory.Ar.Chg.Stalk

theorem regular_along_dominant : ∀ (X X₀ : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (h : X ⟶ X₀) (i : Ω₀ →+* Ω) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i), IsCptGen ξ → (∀ (p : Cpt ξ) (a : Ω₀), a ∈ regAt ξ₀ (pushCpt hd p) → i a ∈ regAt ξ p) ∧ (∀ (p : Cpt ξ) (a : Ω₀), a ∈ regAt ξ₀ (pushCpt hd p) → unitAt ξ p (i a) → unitAt ξ₀ (pushCpt hd p) a) ∧ (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (a : Ω₀) (r : ℂ), genPt ξ ⤳ centre z → ValAt ξ₀ (z ≫ h) a r → ValAt ξ z (i a) r) := by
  intro X X₀ Ω Ω₀ _ _ ξ ξ₀ h i hd hc
  refine ⟨fun p a ha => ?_, fun p a ha hu => ?_, fun z a r hz hv => ?_⟩
  · obtain ⟨hh, h1, -⟩ := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates X₀ Ω₀ ξ₀ X Ω ξ h i hd p
    exact h1 a ha
  · obtain ⟨hh, -, h2⟩ := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates X₀ Ω₀ ξ₀ X Ω ξ h i hd p
    exact h2 hc a ha hu
  · obtain ⟨h0, s, hs1, hs2⟩ := hv
    refine ⟨hz, (Scheme.Hom.stalkMap h (centre z)).hom s, ?_, ?_⟩
    · rw [GlobalTheory.CompanionTheory.Ar.RegAtDom.genMap_stalkMap hd (centre z) hz h0 s]
      exact congrArg i hs1
    · rw [Scheme.stalkClosedPointTo_comp] at hs2
      rw [← hs2]
      rfl

end GlobalTheory.CompanionTheory.Ar.Chg.Stalk
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Crv.Field

theorem curve_field : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (W : Ideal (MRing J)) (p : ℕ) [Fact p.Prime], IsMultiProjPrime W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card B : ℕ) : WithBot ℕ∞) → ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod p) K) (_ : GroundTheory.FunctionField.IsFunctionField (ZMod p) K) (w : (Σ k, J k) → K), mCoordIdeal w = W ∧ Birational w ∧ ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0 :=
  PositivityTheory.HtPt.Ci.curve_field

end GlobalTheory.CompanionTheory.Ar.Crv.Field
end
