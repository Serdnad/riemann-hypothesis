module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle007
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle026
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.genKer_le_ker :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ (c : ι) (D : Type) [CommRing D] [IsLocalRing D] (φ : P →+* D) [IsLocalHom φ] (l : ι → D),
      l c = 1 → (z.map φ).mulVec l = 0 → (∀ j, φ (m j) = l j * φ (m c)) → genKer z m c ≤ RingHom.ker φ := by
  intro P _ _ ι _ _ z m hcot c D _ _ φ _ l hlc hzl hm
  let ψ : MvPolynomial ι P →+* D := MvPolynomial.eval₂Hom φ l
  have hψC : ∀ a, ψ (MvPolynomial.C a) = φ a := fun a => MvPolynomial.eval₂Hom_C φ l a
  have hlam : ∀ j, ψ (UpperTheory.V.AlgebraTools.lam P c j) = l j := by
    intro j
    unfold UpperTheory.V.AlgebraTools.lam
    split_ifs with h
    · subst h
      simp [hlc]
    · exact MvPolynomial.eval₂Hom_X' φ l j
  let M0 : Ideal (MvPolynomial ι P) := Ideal.map MvPolynomial.C (maximalIdeal P)
  haveI hM0 : M0.IsPrime := UpperTheory.V.AlgebraTools.isPrime_map_C (maximalIdeal P)
  let Q : Ideal (MvPolynomial ι P) := Ideal.comap ψ (maximalIdeal D)
  haveI : Q.IsPrime := Ideal.comap_isPrime ψ (maximalIdeal D)
  have hMQ : M0 ≤ Q := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    show ψ (MvPolynomial.C a) ∈ maximalIdeal D
    rw [hψC]
    exact map_nonunit φ a ha
  have hker : chartIdeal z m c ≤ RingHom.ker ψ := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rcases k with i | ⟨j, hj⟩
    · show ψ (((z.map MvPolynomial.C).mulVec (UpperTheory.V.AlgebraTools.lam P c)) i) = 0
      have h := congrFun hzl i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at h ⊢

      rw [map_sum]
      simp only [map_mul, hψC, hlam]
      exact h
    · show ψ (MvPolynomial.C (m j) - UpperTheory.V.AlgebraTools.lam P c j * MvPolynomial.C (m c)) = 0
      rw [map_sub, map_mul, hψC, hψC, hlam, hm j, sub_self]
  have hchartM : chartIdeal z m c ≤ M0 := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rcases k with i | ⟨j, hj⟩
    · show ((z.map MvPolynomial.C).mulVec (UpperTheory.V.AlgebraTools.lam P c)) i ∈ M0
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
      refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
      simpa using hcot.mem (Sum.inl (i, j))
    · show MvPolynomial.C (m j) - UpperTheory.V.AlgebraTools.lam P c j * MvPolynomial.C (m c) ∈ M0
      refine Ideal.sub_mem _ (Ideal.mem_map_of_mem _ ?_) (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_))
      · simpa using hcot.mem (Sum.inr j)
      · simpa using hcot.mem (Sum.inr c)
  have hprime := UpperTheory.V.AlgebraTools.chartIdeal_localization_isPrime P ι z m hcot c Q hMQ
  have hsat : ∀ x, algebraMap (MvPolynomial ι P) (Localization.AtPrime Q) x ∈
      Ideal.map (algebraMap (MvPolynomial ι P) (Localization.AtPrime Q)) (chartIdeal z m c) →
      ∃ t ∉ Q, t * x ∈ chartIdeal z m c := by
    intro x hx
    obtain ⟨t, ht, htx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := Q.primeCompl)
      (S := Localization.AtPrime Q) (chartIdeal z m c) x).mp hx
    exact ⟨t, ht, htx⟩
  intro f hf
  obtain ⟨s, hs, hsf⟩ := hf
  have hmem := Ideal.mem_map_of_mem (algebraMap (MvPolynomial ι P) (Localization.AtPrime Q)) hsf
  rw [map_mul] at hmem
  rcases hprime.mem_or_mem hmem with h | h
  · exfalso
    obtain ⟨t, ht, hts⟩ := hsat s h
    rcases hM0.mem_or_mem (hchartM hts) with h' | h'
    · exact ht (hMQ h')
    · exact hs h'
  · obtain ⟨t, ht, htf⟩ := hsat _ h
    have h0 : ψ (t * MvPolynomial.C f) = 0 := hker htf
    rw [map_mul, hψC] at h0
    have hu : IsUnit (ψ t) := by
      by_contra hn
      exact ht ((IsLocalRing.mem_maximalIdeal _).mpr hn)
    exact (RingHom.mem_ker).mpr ((hu.mul_right_eq_zero).mp h0)
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S]
  {X X' : Type} [AddCommGroup X] [Module R X] [AddCommGroup X'] [Module R X']

private theorem one_tmul_mem (a : Ideal R) {x : X} (hx : x ∈ (a • ⊤ : Submodule R X)) (s : S) :
    s ⊗ₜ[R] x ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X)) := by
  refine Submodule.smul_induction_on hx (fun r hr n _ => ?_) (fun x y hx hy => ?_)
  · rw [TensorProduct.tmul_smul, ← algebraMap_smul S r]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
  · rw [TensorProduct.tmul_add]
    exact add_mem hx hy

private theorem kill_tensor {r : R} (h : ∀ x : X, r • x = 0) (z : S ⊗[R] X) :
    algebraMap R S r • z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact smul_zero _
  | tmul s x =>
    rw [algebraMap_smul, ← TensorProduct.tmul_smul, h x, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

private theorem bot_tensor (a : Ideal R) (h : (a • ⊤ : Submodule R X) = ⊥) :
    (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X)) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro s hs z hz
  clear hz
  rw [Submodule.mem_bot]
  have key : ∀ t ∈ a, ∀ w : S ⊗[R] X, algebraMap R S t • w = 0 := by
    intro t ht w
    apply kill_tensor S
    intro x
    have hm : t • x ∈ (a • ⊤ : Submodule R X) := Submodule.smul_mem_smul ht Submodule.mem_top
    rw [h] at hm
    exact (Submodule.mem_bot R).mp hm
  simp only [Ideal.map] at hs
  induction hs using Submodule.span_induction generalizing z with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    exact key t ht z
  | zero => exact zero_smul _ _
  | add x y _ _ hx hy => rw [add_smul, hx, hy, add_zero]
  | smul c x _ hx => rw [smul_eq_mul, mul_smul, hx, smul_zero]

private theorem ker_tensor (a : Ideal R) (t : X →ₗ[R] X') (ht : Function.Surjective t)
    (hk : LinearMap.ker t = a • ⊤) (h' : (a • ⊤ : Submodule R X') = ⊥) :
    Function.Surjective (t.baseChange S) ∧
      LinearMap.ker (t.baseChange S) = a.map (algebraMap R S) • ⊤ := by
  refine ⟨?_, ?_⟩
  · rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective S ht
  · have hex := lTensor_exact S (LinearMap.exact_subtype_ker_map t) ht
    ext w
    constructor
    · intro hw
      rw [LinearMap.mem_ker, LinearMap.baseChange_eq_ltensor] at hw
      obtain ⟨v, rfl⟩ := (hex w).mp hw
      clear hw
      induction v using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact zero_mem _
      | tmul s x =>
        rw [LinearMap.lTensor_tmul, Submodule.coe_subtype]
        have hx : (x : X) ∈ (a • ⊤ : Submodule R X) := hk ▸ x.2
        exact one_tmul_mem S a hx s
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · intro hw
      have hle : (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X)) ≤
          LinearMap.ker (t.baseChange S) := by
        rw [Submodule.smul_le]
        intro r hr n _
        rw [LinearMap.mem_ker, LinearMap.map_smul]
        have hb := bot_tensor S a h'
        have hm : r • (t.baseChange S) n ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X')) :=
          Submodule.smul_mem_smul hr Submodule.mem_top
        rw [hb] at hm
        exact (Submodule.mem_bot S).mp hm
      exact hle hw

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.exists_patched_module :
    ∀ (R σ : Type) [CommRing R] [Finite σ] (F : Filter ℕ), F ≤ atTop → ∀ (y : σ → R) (m : Ideal R) (f : R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      (S : Type) [CommRing S] [Algebra R S] [IsLocalization.Away f S] (𝔶 : Ideal S), 𝔶 = (Ideal.span (Set.range y)).map (algebraMap R S) →
      (∀ a j : ℕ, ∀ᶠ N in F, QRegAt (M N) y (m ^ j) a) →
      ∀ (Y : Type) [AddCommGroup Y] [Module R Y] [Module S Y] [IsScalarTower R S Y]
        (g : ULim F (fun j => Ideal.span (Set.range y) ⊔ m ^ j) M →ₗ[R] Y) [IsLocalizedModule (Submonoid.powers f) g], Module.Finite S Y →
      ∃ (MM : Type) (_ : AddCommGroup MM) (_ : Module S MM) (_ : Module (AdicCompletion 𝔶 S) MM) (_ : IsScalarTower S (AdicCompletion 𝔶 S) MM)
        (q : MM →ₗ[S] Y), Module.Finite (AdicCompletion 𝔶 S) MM ∧ Function.Surjective q ∧ LinearMap.ker q = 𝔶 • ⊤ ∧
        GlobalTheory.IsQuasiRegularSeq MM (fun s => algebraMap R S (y s)) ∧
        ∀ r : R, (∀ k : ℕ, ∃ e : ℕ, ∀ j : ℕ, ∀ᶠ N in F, ∀ x : M N,
            (f ^ e * r) • x ∈ ((Ideal.span (Set.range y) ^ k ⊔ m ^ j) • ⊤ : Submodule R (M N))) →
          ∀ x : MM, algebraMap R S r • x = 0 := by
  intro R σ _ _ F hF y m f M _ _ S _ _ _ 𝔶 h𝔶 hreg Y _ _ _ _ g _ hfin
  classical
  haveI : Module.Flat R S := IsLocalization.flat S (Submonoid.powers f)
  have haFG : (Ideal.span (Set.range y)).FG := Submodule.fg_span (Set.finite_range y)
  have hFG : 𝔶.FG := h𝔶 ▸ haFG.map _
  have anti : Antitone (fun j : ℕ => m ^ j) := fun i j hij => Ideal.pow_le_pow_right hij
  have hle : ∀ k : ℕ, Ideal.span (Set.range y) ^ (k + 1) ≤ Ideal.span (Set.range y) ^ k :=
    fun k => Ideal.pow_le_pow_right (Nat.le_succ k)
  have htk := fun k : ℕ => ULim.trans_ker R F hF (fun j => m ^ j) M
    (Ideal.span (Set.range y) ^ k) (Ideal.span (Set.range y) ^ (k + 1)) haFG.pow anti (hle k)
  have hS := fun k : ℕ => ker_tensor S (Ideal.span (Set.range y) ^ k) _ (htk k).1 (htk k).2.1 (htk k).2.2
  have hB := fun k : ℕ => bot_tensor S (Ideal.span (Set.range y) ^ k) (htk k).2.2
  have hmap : ∀ k : ℕ, (Ideal.span (Set.range y) ^ k).map (algebraMap R S) = 𝔶 ^ k := by
    intro k
    rw [Ideal.map_pow, h𝔶]
  have key : ∀ I : ℕ → Ideal R, I = (fun j => Ideal.span (Set.range y) ⊔ m ^ j) →
      Nonempty (S ⊗[R] ULim F I M ≃ₗ[S] Y) := by
    rintro I rfl
    exact ⟨(IsLocalizedModule.isBaseChange (Submonoid.powers f) S g).equiv⟩
  obtain ⟨e1⟩ := key (fun j => Ideal.span (Set.range y) ^ 1 ⊔ m ^ j) (by funext j; rw [pow_one])
  haveI := hfin
  haveI : Module.Finite S (S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ 1 ⊔ m ^ j) M) :=
    Module.Finite.equiv e1.symm
  obtain ⟨MM, i1, i2, i3, i4, qq, hfinMM, hsurj, hker, -, hzero⟩ :=
    exists_tower_limit_completion S 𝔶 hFG
      (fun k => S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M)
      (fun k => LinearMap.baseChange S
        (ULim.map F (fun x => sup_le_sup_right (hle k) ((fun j => m ^ j) x)) fun _ => LinearMap.id))
      (fun k => (hS k).1) (fun k => by rw [(hS k).2, hmap]) (fun k => by rw [← hmap]; exact hB k)
      inferInstance
  refine ⟨MM, i1, i2, i3, i4, e1.toLinearMap ∘ₗ qq 1, hfinMM, e1.surjective.comp (hsurj 1), ?_, ?_, ?_⟩
  · rw [LinearEquiv.ker_comp, hker 1, pow_one]
  · have hspan : Ideal.span (Set.range fun s => algebraMap R S (y s)) = 𝔶 := by
      rw [h𝔶, Ideal.map_span, ← Set.range_comp]
      rfl
    refine isQuasiRegularSeq_of_tower S σ (fun s => algebraMap R S (y s)) MM
      (fun k => S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M) qq hsurj
      (fun k => by rw [hker k, hspan]) ?_
    intro b k hbk
    have h1 := qRegAt_uLim R σ F hF (fun j => m ^ j) M y b k anti hbk (fun j => hreg b j)
    haveI : IsLocalizedModule (Submonoid.powers f)
        (TensorProduct.mk R S (ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M) 1) :=
      (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) S _).mpr
        (TensorProduct.isBaseChange R _ S)
    have h2 := (qRegAt_map R S σ y ⊥ b).2 (Submonoid.powers f) _ _
      (TensorProduct.mk R S (ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M) 1) h1
    have h3 := ((qRegAt_map R S σ y ⊥ b).1
      (S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M)).mp h2
    rwa [Ideal.map_bot] at h3
  · intro r hr x
    apply hzero (algebraMap R S r • x)
    intro k
    obtain ⟨e, he⟩ := hr k
    have hP : ∀ z : ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M, (f ^ e * r) • z = 0 :=
      (ULim.scal_eq R ℕ F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M).2.1 (f ^ e * r) he
    have hQ : ∀ w : S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M,
        algebraMap R S (f ^ e * r) • w = 0 := kill_tensor S hP
    have hu := (IsLocalization.Away.algebraMap_isUnit (S := S) f).pow e
    rw [LinearMap.map_smul, ← hu.smul_eq_zero, ← mul_smul, ← map_pow, ← map_mul]
    exact hQ _
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {G : Type} [Group G]

private theorem mem_stab (I : Subgroup G) (z g : G) :
    g ∈ MulAction.stabilizer G (z : G ⧸ I) ↔ z⁻¹ * g * z ∈ I := by
  rw [MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_coe, eq_comm, QuotientGroup.eq, smul_eq_mul, mul_assoc]

private theorem ncard_orb (I K : Subgroup G) (q : G ⧸ I) :
    (MulAction.orbit K q).ncard = (MulAction.stabilizer G q).relIndex K := by
  rw [← MulAction.index_stabilizer]
  rfl

private theorem count (I : Subgroup G) (x y : G)
    (hA : ∀ g ∈ I, (x * y)⁻¹ * g * (x * y) ∈ I → x⁻¹ * g * x ∈ I)
    (hB : ∀ b ∈ I, ∃ b' ∈ I, x * b' * x⁻¹ ∈ I ∧ y⁻¹ * (b'⁻¹ * b) * y ∈ I) :
    (MulAction.orbit I ((x * y : G) : G ⧸ I)).ncard =
      (MulAction.orbit I (x : G ⧸ I)).ncard * (MulAction.orbit I (y : G ⧸ I)).ncard := by
  have h1 : MulAction.orbit (MulAction.stabilizer G (x : G ⧸ I) ⊓ I : Subgroup G) ((x * y : G) : G ⧸ I) =
      (fun q : G ⧸ I => x • q) '' MulAction.orbit I (y : G ⧸ I) := by
    ext q
    constructor
    · rintro ⟨⟨g, hg, hg'⟩, rfl⟩
      refine ⟨_, ⟨⟨x⁻¹ * g * x, (mem_stab I x g).1 hg⟩, rfl⟩, ?_⟩
      show ((x * (x⁻¹ * g * x * y) : G) : G ⧸ I) = ((g * (x * y) : G) : G ⧸ I)
      congr 1
      group
    · rintro ⟨_, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
      obtain ⟨b', hb', h1, h2⟩ := hB b hb
      refine ⟨⟨x * b' * x⁻¹, (mem_stab I x _).2 (by simpa [mul_assoc] using hb'), h1⟩, ?_⟩
      show ((x * b' * x⁻¹ * (x * y) : G) : G ⧸ I) = ((x * (b * y) : G) : G ⧸ I)
      rw [QuotientGroup.eq]
      convert h2 using 1
      group
  have h2 := ncard_orb I (MulAction.stabilizer G (x : G ⧸ I) ⊓ I) ((x * y : G) : G ⧸ I)
  rw [h1, Set.ncard_image_of_injective _ (MulAction.injective x)] at h2
  rw [h2, ncard_orb, ncard_orb, mul_comm, ← Subgroup.inf_relIndex_right (MulAction.stabilizer G (x : G ⧸ I)),
    ← Subgroup.inf_relIndex_right _ (MulAction.stabilizer G (x : G ⧸ I) ⊓ I),
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right inf_le_right,
    ← Subgroup.inf_relIndex_right (MulAction.stabilizer G ((x * y : G) : G ⧸ I))]
  congr 1
  refine le_antisymm (fun g hg => ⟨hg.1, ?_, hg.2⟩) fun g hg => ⟨hg.1, hg.2.2⟩
  exact (mem_stab I x g).2 (hA g hg.2 ((mem_stab I _ g).1 hg.1))

private theorem split_mem {I : Subgroup G} (F : LeviFact I) {u j : G} (hu : u ∈ F.Uf) (hj : j ∈ F.Mf) (h : u * j ∈ I) :
    u ∈ I ∧ j ∈ I := by
  obtain ⟨u', hu', j', hj', l, hl, e⟩ := F.fact _ h
  have := F.uniq (j'⁻¹ * (u'⁻¹ * u) * j'⁻¹⁻¹) (F.M_U _ (inv_mem hj'.1) _ (mul_mem (inv_mem hu'.1) hu)) (j'⁻¹ * j)
    (mul_mem (inv_mem hj'.1) hj) l⁻¹ (inv_mem hl.1) (by
      calc _ = j'⁻¹ * u'⁻¹ * (u * j) * l⁻¹ := by group
        _ = 1 := by rw [e]; group)
  have h2 : j = j' := (inv_mul_eq_one.1 this.2).symm
  have h3 : j ∈ I := h2 ▸ hj'.2
  exact ⟨by simpa using mul_mem h (inv_mem h3), h3⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.leviMul :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G) (F : LeviFact I) (m m' : G), HeckePair I → F.Pos m → F.Pos m' → (F.NormJ m ∨ F.NormJ m') → F.Pos (m * m') ∧ hk ρ I m * hk ρ I m' = hk ρ I (m * m') := by
  intro A G M _ _ _ _ ρ I F m m' hI hm hm' hN
  have hP : F.Pos (m * m') := by
    refine ⟨mul_mem hm.1 hm'.1, fun u hu => ?_, fun l hl => ?_⟩
    · have := hm.2.1 _ ⟨F.M_U _ hm'.1 u hu.1, hm'.2.1 u hu⟩
      convert this using 1
      group
    · have := hm'.2.2 (m⁻¹ * l * m) ⟨by simpa using F.M_L _ (inv_mem hm.1) l hl.1, hm.2.2 l hl⟩
      convert this using 1
      group
  have hB : ∀ b ∈ I, ∃ b' ∈ I, m * b' * m⁻¹ ∈ I ∧ m'⁻¹ * (b'⁻¹ * b) * m' ∈ I := by
    intro b hb
    obtain ⟨u, hu, j, hj, l, hl, rfl⟩ := F.fact b hb
    rcases hN with hN | hN
    · refine ⟨u * j, mul_mem hu.2 hj.2, ?_, ?_⟩
      · convert mul_mem (hm.2.1 u hu) (hN j hj).1 using 1
        group
      · convert hm'.2.2 l hl using 1
        group
    · refine ⟨u, hu.2, hm.2.1 u hu, ?_⟩
      convert mul_mem (hN j hj).2 (hm'.2.2 l hl) using 1
      group
  have hA : ∀ g ∈ I, (m * m')⁻¹ * g * (m * m') ∈ I → m⁻¹ * g * m ∈ I := by
    intro g hg h
    obtain ⟨u, hu, j, hj, l, hl, rfl⟩ := F.fact g hg
    have hU : (m * m')⁻¹ * u * (m * m') ∈ F.Uf := by
      simpa using F.M_U _ (inv_mem hP.1) u hu.1
    have hJ : (m * m')⁻¹ * j * (m * m') ∈ F.Mf := mul_mem (mul_mem (inv_mem hP.1) hj.1) hP.1
    obtain ⟨h1, h2⟩ := split_mem F hU hJ (by
      convert mul_mem h (inv_mem (hP.2.2 l hl)) using 1
      group)
    have h3 : m⁻¹ * u * m ∈ I := by
      convert hm'.2.1 _ ⟨hU, h1⟩ using 1
      group
    have h4 : m⁻¹ * j * m ∈ I := by
      rcases hN with hN | hN
      · exact (hN j hj).2
      · convert (hN _ ⟨hJ, h2⟩).1 using 1
        group
    convert mul_mem (mul_mem h3 h4) (hm.2.2 l hl) using 1
    group
  refine ⟨hP, hkMul A G M ρ I m m' hI (fun b hb => ?_) (count I m m' hA hB)⟩
  obtain ⟨b', -, h1, h2⟩ := hB b hb
  exact ⟨_, h1, _, h2, by group⟩
end
