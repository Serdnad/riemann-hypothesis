module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Mathlib.RingTheory.IsTensorProduct
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle012
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

theorem smul_mem_spanOver (R : Subalgebra o Ω) (S : Set E) {a : Ω} (ha : a ∈ R) {e : E}
    (he : e ∈ spanOver R S) : a • e ∈ spanOver R S := by
  unfold spanOver at he ⊢
  induction he using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, y, hy, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * c, R.mul_mem ha hc, y, hy, by rw [mul_smul]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mem_spanOver_of_mem (R : Subalgebra o Ω) {S : Set E} {e : E} (he : e ∈ S) :
    e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨1, R.one_mem, e, he, (one_smul _ _).symm⟩

theorem frac_add (R : Subalgebra o Ω) {f a b : Ω} (hf : f ∈ R) (ha : ∃ n : ℕ, f ^ n * a ∈ R)
    (hb : ∃ n : ℕ, f ^ n * b ∈ R) : ∃ n : ℕ, f ^ n * (a + b) ∈ R := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨n + m, ?_⟩
  have : f ^ (n + m) * (a + b) = f ^ m * (f ^ n * a) + f ^ n * (f ^ m * b) := by ring
  rw [this]
  exact R.add_mem (R.mul_mem (R.pow_mem hf _) hn) (R.mul_mem (R.pow_mem hf _) hm)

theorem loc_add (R : Subalgebra o Ω) (L : AddSubgroup E) (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L)
    {f : Ω} (hf : f ∈ R) {x y : E} (hx : ∃ n : ℕ, f ^ n • x ∈ L) (hy : ∃ n : ℕ, f ^ n • y ∈ L) :
    ∃ n : ℕ, f ^ n • (x + y) ∈ L := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  refine ⟨n + m, ?_⟩
  have : f ^ (n + m) • (x + y) = f ^ m • (f ^ n • x) + f ^ n • (f ^ m • y) := by
    rw [smul_add, ← mul_smul, ← mul_smul, ← pow_add, ← pow_add, add_comm m n]
  rw [this]
  exact L.add_mem (hL _ (R.pow_mem hf _) _ hn) (hL _ (R.pow_mem hf _) _ hm)

theorem locFree_baseChange {o Ω Ω₁ : Type} [CommRing o] [Field Ω] [Field Ω₁] [Algebra o Ω]
    [Algebra o Ω₁] [Algebra Ω Ω₁] [IsScalarTower o Ω Ω₁] (R : Subalgebra o Ω)
    (R₁ : Subalgebra o Ω₁) (hR : ∀ a ∈ R, algebraMap Ω Ω₁ a ∈ R₁)
    {E E₁ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω₁ E₁] [Module Ω E₁]
    [IsScalarTower Ω Ω₁ E₁] (bc : E →ₗ[Ω] E₁) (hbc : IsBaseChange Ω₁ bc) (r : ℕ)
    (L : AddSubgroup E) (h : LocFree R r L) :
    LocFree R₁ r (spanOver R₁ (bc '' (L : Set E))) := by
  classical
  obtain ⟨hst, k, f, c, hf, hc, hsum, hloc⟩ := h
  have hst₁ : ∀ a ∈ R₁, ∀ e ∈ spanOver R₁ (bc '' (L : Set E)),
      a • e ∈ spanOver R₁ (bc '' (L : Set E)) := fun a ha e he => smul_mem_spanOver R₁ _ ha he
  refine ⟨hst₁, k, fun l => algebraMap Ω Ω₁ (f l), fun l => algebraMap Ω Ω₁ (c l),
    fun l => hR _ (hf l), fun l => hR _ (hc l), ?_, fun l => ?_⟩

  · simp only [← map_mul, ← map_sum, hsum, map_one]
  obtain ⟨b, hli, hsp, hb⟩ := hloc l
  beta_reduce
  set F : Ω₁ := algebraMap Ω Ω₁ (f l) with hF
  have hF₁ : F ∈ R₁ := hR _ (hf l)
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  let B₁ : Module.Basis (Fin r) Ω₁ E₁ := IsBaseChange.basis B hbc
  have hB₁ : (fun q => bc (b q)) = B₁ := by
    funext q
    simp [B₁, B, IsBaseChange.basis_apply]
  have hB₁' : ∀ q, bc (b q) = B₁ q := fun q => congrFun hB₁ q
  refine ⟨B₁, B₁.linearIndependent, B₁.span_eq, fun e => ⟨?_, ?_⟩⟩
  · have key : ∀ x ∈ spanOver R₁ (bc '' (L : Set E)), ∃ a : Fin r → Ω₁,
        (∀ q, ∃ n : ℕ, F ^ n * a q ∈ R₁) ∧ x = ∑ q, a q • B₁ q := by
      intro x hx
      unfold spanOver at hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨t, ht, _, ⟨y, hy, rfl⟩, rfl⟩ := hx
        obtain ⟨a, ha, rfl⟩ := (hb y).1 ⟨0, by simpa using hy⟩
        refine ⟨fun q => t * algebraMap Ω Ω₁ (a q), fun q => ?_, ?_⟩
        · obtain ⟨n, hn⟩ := ha q
          refine ⟨n, ?_⟩
          have := R₁.mul_mem ht (hR _ hn)
          rw [map_mul, map_pow] at this
          convert this using 1
          rw [hF]; ring

        · simp only [map_sum, map_smul, Finset.smul_sum, hB₁', mul_smul, algebraMap_smul]
      | zero => exact ⟨0, fun q => ⟨0, by simp⟩, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨a', ha', rfl⟩ := hy
        exact ⟨a + a', fun q => frac_add R₁ hF₁ (ha q) (ha' q),
          by simp [add_smul, Finset.sum_add_distrib]⟩
      | neg x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        refine ⟨-a, fun q => ?_, by simp⟩
        obtain ⟨n, hn⟩ := ha q
        exact ⟨n, by simpa using R₁.neg_mem hn⟩
    rintro ⟨n, hn⟩
    by_cases h0 : F = 0
    · exact ⟨B₁.repr e, fun q => ⟨1, by simp [h0]⟩, (B₁.sum_repr e).symm⟩
    obtain ⟨a, ha, hea⟩ := key _ hn
    have hFn : F ^ n ≠ 0 := pow_ne_zero _ h0
    refine ⟨fun q => (F ^ n)⁻¹ * a q, fun q => ?_, ?_⟩
    · obtain ⟨m, hm⟩ := ha q
      refine ⟨m + n, ?_⟩
      convert hm using 1
      rw [pow_add]; field_simp
    · simp only [mul_smul, ← Finset.smul_sum]
      rw [← hea, inv_smul_smul₀ hFn]
  · rintro ⟨a, ha, rfl⟩
    refine Finset.sum_induction _
      (fun x : E₁ => ∃ n : ℕ, F ^ n • x ∈ spanOver R₁ (bc '' (L : Set E)))
      (fun x y hx hy => loc_add R₁ _ hst₁ hF₁ hx hy) ⟨0, by simp⟩ (fun q _ => ?_)
    obtain ⟨m, hm⟩ := (hb (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
      by_cases hq : q' = q
      · subst hq; simp
      · simp [hq]⟩, by simp [Pi.single_apply]⟩
    obtain ⟨n, hn⟩ := ha q
    refine ⟨n + m, ?_⟩
    have h1 : bc (f l ^ m • b q) ∈ spanOver R₁ (bc '' (L : Set E)) :=
      mem_spanOver_of_mem R₁ ⟨_, hm, rfl⟩
    have h2 := hst₁ _ hn _ h1
    rw [map_smul, hB₁', ← algebraMap_smul Ω₁ (f l ^ m), map_pow, ← hF, ← mul_smul] at h2
    rw [← mul_smul]
    convert h2 using 2
    ring

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC
end

section

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Crv.SplitProj

open GlobalTheory.CompanionTheory.Ar.Crv

theorem exists_sum_tmul {O k : Type} [CommRing O] [Field k] (z : TensorProduct ℤ k O) :
    ∃ (m : ℕ) (c : Fin m → k) (a : Fin m → O), z = ∑ j, c j ⊗ₜ[ℤ] a j := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul c a => exact ⟨1, fun _ => c, fun _ => a, by simp⟩
  | add x y hx hy =>
    obtain ⟨m, c, a, rfl⟩ := hx
    obtain ⟨n, d, b, rfl⟩ := hy
    refine ⟨m + n, Fin.append c d, Fin.append a b, ?_⟩
    simp [Fin.sum_univ_add]

def splitMap {O k S : Type} [CommRing O] [Field k] (χ : S → (O →+* k)) :
    TensorProduct ℤ k O →ₐ[k] (S → k) :=
  Algebra.TensorProduct.lift (Algebra.ofId k (S → k))
    (Pi.algHom ℤ (fun _ : S => k) fun s => (χ s).toIntAlgHom) (fun _ _ => Commute.all _ _)

theorem splitMap_tmul {O k S : Type} [CommRing O] [Field k] (χ : S → (O →+* k)) (c : k) (a : O)
    (t : S) : splitMap χ (c ⊗ₜ[ℤ] a) t = c * χ t a := by
  simp [splitMap, Algebra.ofId_apply]

def actMap {K V O k : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] [Field k]
    [Algebra k K] (ρ : O →+* Module.End K V) : TensorProduct ℤ k O →ₐ[ℤ] Module.End K V :=
  Algebra.TensorProduct.lift
    ((algebraMap K (Module.End K V)).comp (algebraMap k K)).toIntAlgHom ρ.toIntAlgHom
    (fun c a => show Commute (algebraMap K (Module.End K V) (algebraMap k K c)) (ρ a) from
      Algebra.commute_algebraMap_left _ _)

theorem actMap_tmul {K V O k : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] [Field k]
    [Algebra k K] (ρ : O →+* Module.End K V) (c : k) (a : O) :
    actMap ρ (c ⊗ₜ[ℤ] a) = algebraMap k K c • ρ a := by
  rw [Algebra.smul_def]
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem smul_mem_of_isBun {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V]
    [Module K V] {L : C.I → AddSubgroup V} (hL : IsBun C L) (i : C.I) {c : K}
    (hc : C.v i c ≤ 1) {x : V} (hx : x ∈ L i) : c • x ∈ L i := by
  obtain ⟨b, hb⟩ := hL.1 i
  refine (hb _).2 fun q => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_one' hc ((hb _).1 hx q)

theorem split_proj : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k]
    [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ →
    (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L →
    (∀ a, IsHom C L L (ρ a)) →
    ∃ e : S → Module.End K V, (∀ s, IsHom C L L (e s)) ∧
      (∀ s x, e s x ∈ (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a)))) ∧
      (∀ s, ∀ x ∈ (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))), e s x = x) ∧
      (∀ x, ∑ s, e s x = x) ∧
      ∀ s, ∃ (m : ℕ) (c : Fin m → k) (a : Fin m → O),
        (∀ t, ∑ j, c j * χ t (a j) = if t = s then 1 else 0) ∧
        e s = ∑ j, algebraMap k K (c j) • ρ (a j) := by
  intro K _ C V _ _ _ L O k S _ _ _ _ _ χ hχ hk ρ hL hρ
  have hinj : Function.Injective (splitMap χ) := hχ.1
  have hsurj : Function.Surjective (splitMap χ) := hχ.2
  choose z hz using fun s : S => hsurj (Pi.single s 1)
  choose m c a hza using fun s : S => exists_sum_tmul (z s)
  have he : ∀ s, actMap (k := k) ρ (z s) = ∑ j, algebraMap k K (c s j) • ρ (a s j) := by
    intro s

    rw [hza s, map_sum]
    exact Finset.sum_congr rfl fun j _ => actMap_tmul ρ _ _
  have hcoef : ∀ s t, ∑ j, c s j * χ t (a s j) = if t = s then 1 else 0 := by
    intro s t
    have h := congrFun (hz s) t

    rw [hza s, map_sum, Finset.sum_apply] at h
    simp only [splitMap_tmul] at h
    rw [h, Pi.single_apply]
  have hmul : ∀ s b, ρ b * actMap (k := k) ρ (z s) =
      algebraMap k K (χ s b) • actMap (k := k) ρ (z s) := by
    intro s b
    have h : ((1 : k) ⊗ₜ[ℤ] b) * z s = (χ s b ⊗ₜ[ℤ] (1 : O)) * z s := by
      apply hinj
      rw [map_mul, map_mul, hz s]
      funext t
      simp only [Pi.mul_apply, splitMap_tmul, Pi.single_apply]
      by_cases hts : t = s
      · subst hts; simp
      · simp [hts]
    have h' := congrArg (actMap (k := k) ρ) h
    rw [map_mul, map_mul, actMap_tmul, actMap_tmul] at h'
    simpa using h'
  have hsum : ∑ s, actMap (k := k) ρ (z s) = 1 := by
    have h : ∑ s, z s = 1 := by
      apply hinj

      rw [map_sum, map_one]
      simp only [hz]
      funext t
      simp [Finset.sum_apply, Pi.single_apply]

    rw [← map_sum, h, map_one]
  refine ⟨fun s => actMap (k := k) ρ (z s), ?_, ?_, ?_, ?_, ?_⟩
  · intro s i x hx
    show actMap (k := k) ρ (z s) x ∈ L i
    rw [he s, LinearMap.sum_apply]
    exact sum_mem fun j _ => smul_mem_of_isBun C hL i (hk i _) (hρ _ i x hx)
  · intro s x
    simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker]
    intro b
    have h := congrArg (fun f : Module.End K V => f x) (hmul s b)
    simpa [sub_eq_zero] using h
  · intro s x hx
    simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    have hx' : ∀ b, ρ b x = algebraMap k K (χ s b) • x := fun b => by
      simpa [sub_eq_zero] using hx b
    show actMap (k := k) ρ (z s) x = x
    rw [he s, LinearMap.sum_apply]
    have : ∀ j, (algebraMap k K (c s j) • ρ (a s j)) x =
        algebraMap k K (c s j * χ s (a s j)) • x := fun j => by
      rw [LinearMap.smul_apply, hx', smul_smul, map_mul]
    simp only [this]

    rw [← Finset.sum_smul, ← map_sum, hcoef s s]
    simp
  · intro x
    have h := congrArg (fun f : Module.End K V => f x) hsum
    simpa [LinearMap.sum_apply] using h
  · intro s
    exact ⟨m s, c s, a s, hcoef s, he s⟩

end GlobalTheory.CompanionTheory.Ar.Crv.SplitProj
end
end

section

namespace GlobalTheory.CompanionTheory.FinPresDescent

theorem finiteType_of_finite_projective (R C D : Type*) [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra C D] [Algebra R D] [IsScalarTower R C D]
    [Module.Finite C D] [Module.Projective C D] (hinj : Function.Injective (algebraMap C D))
    [Algebra.FiniteType R D] : Algebra.FiniteType R C :=
  _root_.UpperTheory.Reformulated.B.FiniteTypeDescent.main R C D hinj

theorem ker_fg_of_projective {P C M : Type*} [CommRing P] [CommRing C] [Algebra P C]
    [AddCommGroup M] [Module P M] [Module C M] [IsScalarTower P C M]
    (hsurj : Function.Surjective (algebraMap P C))
    [Module.FinitePresentation P M] [Module.Projective C M]
    (faith : ∀ c : C, (∀ m : M, c • m = 0) → c = 0) :
    (RingHom.ker (algebraMap P C)).FG := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' P M
  have hker : (LinearMap.ker π).FG := Module.FinitePresentation.fg_ker π hπ
  let b : Fin n → M := fun i => π (Pi.single i 1)
  have hπb : ∀ x, π x = ∑ i, x i • b i := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ π x]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ext j
    simp [b, Pi.single_apply, eq_comm]
  have hπC : ∀ x, π x = ∑ i, algebraMap P C (x i) • b i := fun x => by
    rw [hπb]
    simp only [algebraMap_smul]
  let πC : (Fin n → C) →ₗ[C] M := Fintype.linearCombination C b
  have hπCs : Function.Surjective πC := by
    intro m
    obtain ⟨x, rfl⟩ := hπ m
    refine ⟨fun i => algebraMap P C (x i), ?_⟩
    rw [hπC, Fintype.linearCombination_apply]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property πC LinearMap.id hπCs
  have hs' : ∀ m, ∑ i, s m i • b i = m := fun m => by
    have := LinearMap.congr_fun hs m
    simpa [πC, Fintype.linearCombination_apply] using this
  choose v hv using fun (p : Fin n × Fin n) => hsurj (s (b p.1) p.2)
  let E : (Fin n → P) → Fin n → P := fun x j => ∑ i, x i * v (i, j)
  have key1 : ∀ x j, algebraMap P C (E x j) = s (π x) j := fun x j => by
    have hsx : s (π x) = ∑ i, algebraMap P C (x i) • s (b i) := by

      rw [hπC, map_sum]
      simp only [map_smul]
    rw [hsx, Finset.sum_apply]

    simp only [E, map_sum, map_mul, hv, Pi.smul_apply, smul_eq_mul]
  have key2 : ∀ x, π (fun j => E x j) = π x := fun x => by
    rw [hπC]
    simp only [key1]
    exact hs' _
  obtain ⟨G, hG⟩ := hker
  let I₀ : Ideal P := Ideal.span ((fun q : (Fin n → P) × Fin n => E q.1 q.2) ''
    ((G : Set (Fin n → P)) ×ˢ Set.univ))
  have hI₀ : I₀.FG := ⟨(G ×ˢ Finset.univ).image (fun q : (Fin n → P) × Fin n => E q.1 q.2), by
    simp [I₀]⟩
  have key3 : ∀ x ∈ LinearMap.ker π, ∀ j, E x j ∈ I₀ := by
    intro x hx j
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Ideal.subset_span ⟨(x, j), ⟨hx, trivial⟩, rfl⟩
    | zero => simp [E]
    | add x y _ _ hx hy =>
      have : E (x + y) j = E x j + E y j := by simp [E, add_mul, Finset.sum_add_distrib]
      rw [this]; exact I₀.add_mem hx hy
    | smul t x _ hx =>
      have : E (t • x) j = t * E x j := by simp [E, Finset.mul_sum, mul_assoc]
      rw [this]; exact I₀.mul_mem_left t hx
  let T : Ideal P := Ideal.span (Set.range v)
  have hET : ∀ x j, E x j ∈ T := fun x j =>
    T.sum_mem fun i _ => T.mul_mem_left _ (Ideal.subset_span ⟨(i, j), rfl⟩)
  have hle : (⊤ : Submodule P M) ≤ T • (⊤ : Submodule P M) := by
    intro m _
    obtain ⟨x, rfl⟩ := hπ m
    rw [← key2, hπb]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hET x i) trivial
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul T ⊤
    Module.Finite.fg_top hle
  have hrI : r ∈ RingHom.ker (algebraMap P C) := by
    rw [RingHom.mem_ker]
    refine faith _ fun m => ?_
    rw [algebraMap_smul]
    exact hr0 m trivial
  have key5 : ∀ a ∈ RingHom.ker (algebraMap P C), ∀ p, a * v p ∈ I₀ := by
    rintro a ha ⟨i, j⟩
    have hx : (Pi.single i a : Fin n → P) ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, hπC]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = i
      · subst hk
        rw [Pi.single_eq_same, RingHom.mem_ker.1 ha, zero_smul]
      · rw [Pi.single_eq_of_ne hk, map_zero, zero_smul]
    have := key3 _ hx j
    simpa [E, Pi.single_apply] using this
  have key6 : ∀ a ∈ RingHom.ker (algebraMap P C), ∀ t ∈ T, a * t ∈ I₀ := by
    intro a ha t ht
    induction ht using Submodule.span_induction with
    | mem t ht => obtain ⟨p, rfl⟩ := ht; exact key5 a ha p
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact I₀.add_mem hx hy
    | smul c x _ hx =>
      rw [smul_eq_mul, mul_left_comm]; exact I₀.mul_mem_left c hx
  have hI₀le : I₀ ≤ RingHom.ker (algebraMap P C) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨g, j⟩, ⟨hg, -⟩, rfl⟩
    have hgk : g ∈ LinearMap.ker π := by
      rw [← hG]; exact Submodule.subset_span hg
    change algebraMap P C (E g j) = 0
    rw [key1, LinearMap.mem_ker.1 hgk, map_zero]
    rfl
  have heq : RingHom.ker (algebraMap P C) = I₀ ⊔ Ideal.span {r} := by
    apply le_antisymm
    · intro a ha
      have h1 : a * (r - 1) ∈ I₀ := key6 a ha _ hr
      have h2 : a * r ∈ Ideal.span {r} := Ideal.mul_mem_left _ a (Ideal.mem_span_singleton_self r)
      have : a = a * r + -(a * (r - 1)) := by ring
      rw [this]
      exact Submodule.add_mem_sup h2 (I₀.neg_mem h1) |> fun h => by
        rw [sup_comm]; exact h
    · refine sup_le hI₀le ?_
      rw [Ideal.span_singleton_le_iff_mem]
      exact hrI
  rw [heq]
  exact Submodule.FG.sup hI₀ (Submodule.fg_span_singleton r)

end GlobalTheory.CompanionTheory.FinPresDescent


open GlobalTheory.CompanionTheory.FinPresDescent in
theorem GlobalTheory.CompanionTheory.FinPresDescent.finitePresentation_of_finite_projective_faithfullyFlat :
    ∀ (R C D : Type) [CommRing R] [CommRing C] [CommRing D] [Algebra R C] [Algebra C D]
      [Algebra R D] [IsScalarTower R C D], Module.Finite C D → Module.Projective C D →
      Module.FaithfullyFlat C D → Algebra.FinitePresentation R D →
      Algebra.FinitePresentation R C := by
  intro R C D _ _ _ _ _ _ _ hfin hproj hff hfp
  have hinj : Function.Injective (algebraMap C D) := FaithfulSMul.algebraMap_injective C D
  haveI : Algebra.FiniteType R D := inferInstance
  haveI : Algebra.FiniteType R C := finiteType_of_finite_projective R C D hinj
  obtain ⟨k, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType R C›
  letI : Algebra (MvPolynomial (Fin k) R) C := f.toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin k) R) D := ((algebraMap C D).comp f.toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin k) R) C D := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R (MvPolynomial (Fin k) R) D := .of_algebraMap_eq fun r => by
    change algebraMap R D r = algebraMap C D (f (algebraMap R _ r))
    rw [f.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.FinitePresentation (MvPolynomial (Fin k) R) D :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ D
  haveI : Module.Finite (MvPolynomial (Fin k) R) C :=
    Module.Finite.of_surjective (Algebra.linearMap _ C) hf
  haveI : Module.Finite (MvPolynomial (Fin k) R) D := Module.Finite.trans C D
  haveI : Module.FinitePresentation (MvPolynomial (Fin k) R) D :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ D
  have hker := ker_fg_of_projective (P := MvPolynomial (Fin k) R) (C := C) (M := D) hf
    (fun c hc => hinj (by simpa [Algebra.smul_def] using hc 1))
  exact ⟨k, f, hf, hker⟩
end
