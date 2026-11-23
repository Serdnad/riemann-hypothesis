module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
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
public import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Localization.Finiteness

@[expose] public section

section

private theorem UpperTheory.Reformulated.B.LevelOfCongruence.level {C R T : Type} [CommRing C] [CommRing R] [CommRing T]
    (a : C →+* R) (f : C →+* T) (M : Ideal R) (K : Ideal T)
    (hd : ∀ r : R, ∃ c, r - a c ∈ M) (hk : ∀ c, a c ∈ M → f c ∈ K) :
    ∃ g : R →+* T ⧸ K, ∀ r c, r - a c ∈ M → g r = Ideal.Quotient.mk K (f c) := by
  have hs : Function.Surjective ((Ideal.Quotient.mk M).comp a) := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := hd r
    exact ⟨c, (Ideal.Quotient.eq.2 hc).symm⟩
  have hker : RingHom.ker ((Ideal.Quotient.mk M).comp a) ≤
      RingHom.ker ((Ideal.Quotient.mk K).comp f) := by
    intro c hc
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hc ⊢
    exact hk c hc
  refine ⟨(RingHom.liftOfSurjective _ hs ⟨_, hker⟩).comp (Ideal.Quotient.mk M), ?_⟩
  intro r c hc
  rw [RingHom.comp_apply, Ideal.Quotient.eq.2 hc]
  exact RingHom.liftOfSurjective_comp_apply _ hs ⟨_, hker⟩ c

theorem UpperTheory.Reformulated.B.LevelOfCongruence.cu_ex :
    ∀ {C R : Type} [inst : CommRing C] [inst_1 : CommRing R] [inst_2 : Algebra C R] [inst_3 : IsLocalRing R] {x : Ideal C},
      UpperTheory.V.CA.IsCplAt x R →
        ∀ {T : Type} [inst_4 : CommRing T] (J : Ideal T) [IsAdicComplete J T] (f : C →+* T),
          x ≤ Ideal.comap f J →
            ∃ (F : R →+* T), F.comp (Algebra.algebraMap C R) = f ∧ IsLocalRing.maximalIdeal R ≤ Ideal.comap F J := by
  intro C R _ _ _ _ x h T _ J _ f hx
  have hk : ∀ (n : ℕ) (c : C), algebraMap C R c ∈ IsLocalRing.maximalIdeal R ^ n → f c ∈ J ^ n := by
    intro n c hc
    have h1 : c ∈ x ^ n := by
      rw [← h.comap_pow n]
      exact hc
    exact Ideal.le_comap_pow f n (Ideal.pow_right_mono hx n h1)
  choose g hg using fun n : ℕ => UpperTheory.Reformulated.B.LevelOfCongruence.level (algebraMap C R) f
    (IsLocalRing.maximalIdeal R ^ n) (J ^ n) (h.dense n) (hk n)
  have hc : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp (g n) = g m := by
    intro m n hle
    ext r
    obtain ⟨c, hc⟩ := h.dense n r
    rw [RingHom.comp_apply, hg n r c hc, hg m r c (Ideal.pow_le_pow_right hle hc)]
    rfl
  refine ⟨IsAdicComplete.liftRingHom J g hc, ?_, ?_⟩
  · apply DFunLike.coe_injective
    apply IsHausdorff.funext' J
    intro n c
    rw [RingHom.comp_apply, IsAdicComplete.mk_liftRingHom]
    exact hg n _ c (by simp)
  · intro r hr
    have h0 := IsAdicComplete.mk_liftRingHom J g hc 1 r
    rw [hg 1 r 0 (by simpa using hr), map_zero, map_zero, Ideal.Quotient.eq_zero_iff_mem,
      pow_one] at h0
    exact h0
end

section

private theorem UpperTheory.Reformulated.B.G5.irr_conj {G R : Type} [Group G] [CommRing R] {m : ℕ}
    {U : Subgroup G} {a a' : G → Matrix (Fin m) (Fin m) R} (P Q : Matrix (Fin m) (Fin m) R)
    (hPQ : P * Q = 1) (H : ∀ g ∈ U, a g = Q * a' g * P)
    (hirr : ∀ S : Submodule R (Fin m → R),
      (∀ g ∈ U, ∀ v ∈ S, (a g).mulVec v ∈ S) → S = ⊥ ∨ S = ⊤)
    (S : Submodule R (Fin m → R)) (hS : ∀ g ∈ U, ∀ v ∈ S, (a' g).mulVec v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  have key : ∀ v : Fin m → R, P.mulVec (Q.mulVec v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
  have mem : ∀ v : Fin m → R, v ∈ S.comap P.mulVecLin ↔ P.mulVec v ∈ S := fun v => Iff.rfl
  have hst : ∀ g ∈ U, ∀ v ∈ S.comap P.mulVecLin, (a g).mulVec v ∈ S.comap P.mulVecLin := by
    intro g hg v hv
    rw [mem] at hv ⊢
    rw [H g hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, key]
    exact hS g hg _ hv
  rcases hirr _ hst with h0 | h1
  · left
    rw [eq_bot_iff]
    intro v hv
    have h2 : Q.mulVec v ∈ S.comap P.mulVecLin := by rw [mem, key]; exact hv
    rw [h0, Submodule.mem_bot] at h2
    rw [Submodule.mem_bot, ← key v, h2, Matrix.mulVec_zero]
  · right
    rw [eq_top_iff]
    intro v _
    have h2 : Q.mulVec v ∈ S.comap P.mulVecLin := by rw [h1]; exact Submodule.mem_top
    rwa [mem, key] at h2

theorem UpperTheory.Reformulated.B.G5.matIrr_conj :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ}
    {U : Subgroup G} {a a' : G → Matrix (Fin m) (Fin m) R} (h : GL (Fin m) R),
    (∀ g ∈ U, a g = (↑h⁻¹ : Matrix (Fin m) (Fin m) R) * a' g * (↑h : Matrix (Fin m) (Fin m) R)) →
      UpperTheory.V.U3.MatIrr U a → UpperTheory.V.U3.MatIrr U a' := by
  intro G R _ _ m U a a' h H hirr
  exact UpperTheory.Reformulated.B.G5.irr_conj _ _ (Units.mul_inv h) H hirr
end

section

open GlobalTheory.CompanionTheory.Ar.Num in
private theorem mem_spanOver_of_mem_span {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    {E : Type} [AddCommGroup E] [Module Ω E] (R : Subalgebra o Ω) (S : Set E) {v : E}
    (hv : v ∈ Submodule.span R S) : v ∈ spanOver R S := by
  obtain ⟨m, a, g, rfl⟩ := Submodule.mem_span_set'.1 hv
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
  exact ⟨(a i : Ω), (a i).2, (g i : E), (g i).2, rfl⟩

open GlobalTheory.CompanionTheory.Ar.Num in
private theorem exists_finset_span_of_locFree {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    {E : Type} [AddCommGroup E] [Module Ω E] (R : Subalgebra o Ω) (N : ℕ) (L : AddSubgroup E)
    (h : LocFree R N L) :
    ∃ T : Finset E, (∀ t ∈ T, t ∈ L) ∧ ∀ e ∈ L, e ∈ Submodule.span R (T : Set E) := by
  classical
  obtain ⟨-, k, f, c, hf, hc, hsum, hb⟩ := h
  choose b _ _ hb using hb
  have hgen : ∀ l q, ∃ m : ℕ, f l ^ m • b l q ∈ L := by
    intro l q
    refine (hb l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases hq : q' = q
      · subst hq
        simpa using R.one_mem
      · simpa [Pi.single_eq_of_ne hq] using R.zero_mem
    · simp [Pi.single_apply]
  choose m hm using hgen
  refine ⟨Finset.univ.image fun x : Fin k × Fin N => f x.1 ^ m x.1 x.2 • b x.1 x.2, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ht
    exact hm x.1 x.2
  · intro e he
    let f' : Fin k → R := fun l => ⟨f l, hf l⟩
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (Set.range f') ?_ e ?_
    · rw [Ideal.eq_top_iff_one]
      have h1 : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * f' l := by
        apply Subtype.ext
        simpa [f'] using hsum.symm
      rw [h1]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
    · rintro ⟨_, l, rfl⟩
      obtain ⟨a, ha, hea⟩ := (hb l e).1 ⟨0, by simpa using he⟩
      choose j hj using ha
      refine ⟨∑ q, (j q + m l q), ?_⟩
      rw [hea, Finset.smul_sum]
      refine Submodule.sum_mem _ fun q _ => ?_
      have hle : j q + m l q ≤ ∑ q, (j q + m l q) :=
        Finset.single_le_sum (f := fun q => j q + m l q) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ q)
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      have heq : (f' l ^ (∑ q, (j q + m l q))) • a q • b l q =
          (f' l ^ d * (⟨f l ^ j q * a q, hj q⟩ : R)) • (f l ^ m l q • b l q) := by
        rw [hd]
        change (f l ^ (j q + m l q + d)) • a q • b l q =
          (f l ^ d * (f l ^ j q * a q)) • (f l ^ m l q • b l q)
        rw [smul_smul, smul_smul]
        congr 1
        ring
      change (f' l ^ (∑ q, (j q + m l q))) • a q • b l q ∈ _
      rw [heq]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨(l, q), Finset.mem_univ _, rfl⟩)

open GlobalTheory.CompanionTheory.Ar.Num in
private theorem linMap_injective {Ω : Type} [Field Ω] {F : Type} [Zero F] [One F] (n : ℕ)
    (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) : LinearMap.ker (linMap n χ) = ⊥ := by
  classical
  rw [LinearMap.ker_eq_bot']
  intro l hl
  funext i
  have h := congrFun hl (Pi.single i 1)
  simp only [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply] at h
  rw [Finset.sum_eq_single i] at h
  · simpa [h1] using h
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj, h0]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem UpperTheory.Reformulated.B.AffineGenerators.af_gens :
    ∀ {o Ω : Type} [inst : CommRing o] [inst_1 : Field Ω] [inst_2 : Algebra o Ω] {F : Type} [inst_3 : Zero F]
      [inst_4 : One F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : GlobalTheory.CompanionTheory.Ar.Num.LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω)
      (p N : ℕ) (χ : F → Ω),
      χ (0 : F) = (0 : Ω) →
        χ (1 : F) = (1 : Ω) →
          GlobalTheory.CompanionTheory.Ar.Num.LocFree R N (D.l1 R p) →
            GlobalTheory.CompanionTheory.Ar.Num.Summand (D.l1 R p) (GlobalTheory.CompanionTheory.Ar.Num.linMap n χ).range →
              ∃ (S : Finset (Fin n → Ω)),
                (↑S : Set (Fin n → Ω)) ⊆ (↑(D.af R p χ) : Set (Fin n → Ω)) ∧
                  D.af R p χ ≤ GlobalTheory.CompanionTheory.Ar.Num.spanOver R (↑S : Set (Fin n → Ω)) := by
  intro o Ω _ _ _ F _ _ n Sg r s D R p N χ h0 h1 hfree hsum
  classical
  obtain ⟨T, hT, hspan⟩ := exists_finset_span_of_locFree R N _ hfree
  obtain ⟨ρ, hρU, hρid, hρL⟩ := hsum
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (linMap_injective n χ h0 h1)
  have hg' : ∀ l, g (GlobalTheory.CompanionTheory.Ar.Num.linMap n χ l) = l := fun l => LinearMap.congr_fun hg l
  refine ⟨T.image fun t => g (ρ t), ?_, ?_⟩
  · intro v hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hv)
    obtain ⟨l, hl⟩ := hρU t
    change GlobalTheory.CompanionTheory.Ar.Num.linMap n χ (g (ρ t)) ∈ D.l1 R p
    rw [← hl, hg', hl]
    exact hρL t (hT t ht)
  · intro l hl
    have hl' : GlobalTheory.CompanionTheory.Ar.Num.linMap n χ l ∈ D.l1 R p := hl
    have hmem := Submodule.apply_mem_span_image_of_mem_span
      ((g ∘ₗ ρ).restrictScalars R) (hspan _ hl')
    apply mem_spanOver_of_mem_span
    rw [Finset.coe_image]
    have heq : ((g ∘ₗ ρ).restrictScalars R) (GlobalTheory.CompanionTheory.Ar.Num.linMap n χ l) = l := by
      change g (ρ (GlobalTheory.CompanionTheory.Ar.Num.linMap n χ l)) = l
      rw [hρid _ ⟨l, rfl⟩, hg']
    rw [heq] at hmem
    exact hmem
end

section

open Matrix in
private theorem hpk_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  have key : ∀ i : Fin (2 * r + k + 1), ∃ s : Fin (2 * r + k + 1),
      (s.val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) := fun i =>
    ⟨⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by
      have := i.isLt; split_ifs <;> omega⟩, rfl⟩
  ext i l
  obtain ⟨s, hs⟩ := key i
  have hi := i.isLt
  have hl := l.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · simp only [Formalism.QuantumDeterminants.Hpk, Matrix.one_apply, Fin.ext_iff]
    split_ifs at hs ⊢ <;> first | omega | norm_num
  · intro j _ hj
    have hj' : j.val ≠ s.val := fun h => hj (Fin.ext h)
    have hjl := j.isLt
    have : Formalism.QuantumDeterminants.Hpk k r i j = 0 := by
      simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
      split_ifs at hs ⊢ <;> first | omega | rfl
    rw [this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ s) h
end

section

namespace UpperTheory.Reformulated.B.Qh15

theorem aux1 : ∀ {A : Type} [inst : CommRing A], SMulCommClass A A A := by
  intro A _
  infer_instance

theorem aux2 : ∀ {G A : Type} [inst : Group G] [inst_1 : CommRing A] (κ : G →* Aˣ),
  (↑(κ 1) : A) • (LinearMap.id : A →ₗ[A] A) = 1 := by
  intro G A _ _ κ
  ext
  simp

theorem aux3 : ∀ {G A : Type} [inst : Group G] [inst_1 : CommRing A] (κ : G →* Aˣ)
  (g h : G), (↑(κ (g * h)) : A) • (LinearMap.id : A →ₗ[A] A) =
    ((↑(κ g) : A) • LinearMap.id) * ((↑(κ h) : A) • LinearMap.id) := by
  intro G A _ _ κ g h
  ext
  simp [mul_comm]

noncomputable def chRep : {G A : Type} →
  [inst : Group G] → [inst_1 : CommRing A] → (G →* Aˣ) → Representation A G A :=
  fun {G A} [Group G] [CommRing A] κ =>
    { toFun := fun g => ↑(κ g) • LinearMap.id, map_one' := aux2 κ,
      map_mul' := aux3 κ }

theorem act_mul : ∀ {G : Type} [inst : Group G] {Qp K₀ K : Type} [inst_1 : Field Qp]
  [inst_2 : Field K₀] [inst_3 : Field K] [inst_4 : Algebra Qp K₀] [inst_5 : Algebra Qp K] [inst_6 : Algebra K₀ K]
  [inst_7 : IsScalarTower Qp K₀ K] {B BdR : Type} [inst_8 : CommRing B] [inst_9 : CommRing BdR] [inst_10 : Algebra Qp B]
  [inst_11 : Algebra K₀ B] [inst_12 : IsScalarTower Qp K₀ B] [inst_13 : Algebra Qp BdR] [inst_14 : Algebra K₀ BdR]
  [inst_15 : Algebra K BdR] [inst_16 : IsScalarTower Qp K BdR] [inst_17 : IsScalarTower K₀ K BdR]
  [inst_18 : IsScalarTower Qp K₀ BdR] (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {E : Type}
  [inst_19 : Field E] [inst_20 : Algebra Qp E] (κ : G →* Eˣ) (g : G) (x y : TensorProduct Qp E B),
  (Formalism.WeaklyAdmissibleFiltrations.actVB PD (chRep κ) g) x *
      (Formalism.WeaklyAdmissibleFiltrations.actVB PD (chRep κ⁻¹) g) y =
    (Formalism.WeaklyAdmissibleFiltrations.actVB PD (chRep 1) g) (x * y) := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD E _ _ κ g x y
  have hch : ∀ (μ : G →* Eˣ) (a : E), chRep μ g a = (μ g : E) * a :=
    fun μ a => rfl
  have hact : ∀ (μ : G →* Eˣ) (a : E) (b : B),
      Formalism.WeaklyAdmissibleFiltrations.actVB PD (chRep μ) g (a ⊗ₜ[Qp] b) =
        ((μ g : E) * a) ⊗ₜ[Qp] PD.actB g b := by
    intro μ a b
    rw [← hch]
    rfl
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_mul]
  | add x₁ x₂ h₁ h₂ => simp only [map_add (f := _), add_mul, h₁, h₂]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | add y₁ y₂ h₁ h₂ => simp only [map_add (f := _), mul_add, h₁, h₂]
    | tmul c d =>
      have hu : (κ g : E) * a * ((κ⁻¹ g : E) * c) = ((1 : G →* Eˣ) g : E) * (a * c) := by
        rw [mul_mul_mul_comm, ← Units.val_mul, MonoidHom.inv_apply, mul_inv_cancel,
          MonoidHom.one_apply]
      rw [Algebra.TensorProduct.tmul_mul_tmul, hact, hact, hact,
        Algebra.TensorProduct.tmul_mul_tmul, hu, map_mul]

end UpperTheory.Reformulated.B.Qh15
end

section

open TensorProduct Formalism.WeaklyAdmissibleFiltrations in
theorem UpperTheory.Reformulated.B.Qf14.phi_mul
    {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR]
    [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {E : Type} [Field E] [Algebra Qp E]
    (x y : E ⊗[Qp] B) :
    φVB PD (LL := E) (V := E) (x * y) =
      φVB PD (LL := E) (V := E) x * φVB PD (LL := E) (V := E) y := by
  have h : ∀ z : E ⊗[Qp] B,
      φVB PD (LL := E) (V := E) z = Algebra.TensorProduct.map (AlgHom.id E E) PD.φ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b => rfl
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  exact (h (x * y)).trans ((map_mul _ x y).trans (congrArg₂ (· * ·) (h x).symm (h y).symm))
end

section

open Formalism.WeaklyAdmissibleFiltrations in
theorem UpperTheory.Reformulated.B.Ue16.exists_smul_mem
    {G : Type} [inst : Group G] {LL : Type} [inst_1 : Field LL] {O : Type} [inst_2 : CommRing O]
    [inst_3 : Algebra O LL] [IsDomain O] [IsFractionRing O LL] {V : Type}
    [inst_6 : AddCommGroup V] [inst_7 : Module LL V] [inst_8 : Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (x : V) :
    ∃ a : O, a ≠ 0 ∧ a • x ∈ L.T := by
  have hx : x ∈ Submodule.span LL (L.T : Set V) := by
    rw [L.span]
    exact Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) LL (L.T : Set V) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩
end

section

namespace UpperTheory.Reformulated.B.Qe28

@[reducible] noncomputable def FDSec : {E : Type} →
  [inst : Field E] →
    [inst_1 : NumberField E] →
      [inst_2 : NumberField.IsCMField E] →
        {r : ℕ} → {Comp : Type} → (Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r) → Type :=
  fun {E} [Field E] [NumberField E] [NumberField.IsCMField E] {r} {Comp} X =>
    (c : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Frame (X c).Ψ r → ℂ

noncomputable def IsHolCusp : {E : Type} →
  [inst : Field E] →
    [inst_1 : NumberField E] →
      [inst_2 : NumberField.IsCMField E] →
        {r : ℕ} →
          {Comp : Type} →
            (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r) →
              ((c : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r) →
                FDSec X → Prop :=
  fun {E} [Field E] [NumberField E] [NumberField.IsCMField E] {r} {Comp} X la P => ∀ (c : Comp), P c ∈ (X c).SS (la c)

noncomputable def holSub : {E : Type} →
  [inst : Field E] →
    [inst_1 : NumberField E] →
      [inst_2 : NumberField.IsCMField E] →
        {r : ℕ} →
          {Comp : Type} →
            (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r) →
              ((c : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r) →
                Submodule ℂ (FDSec X) :=
  fun {E} [Field E] [NumberField E] [NumberField.IsCMField E] {r} {Comp} X la =>
    Submodule.span ℂ {P | IsHolCusp X la P}

theorem holSub_mul : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
  [inst_2 : NumberField.IsCMField E] {r : ℕ},
  ReciprocityTheory.ChartRestriction.G.FD.SiegelSpaceAlgebra (E := E) →
    ∀ {Comp : Type} {X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r}
      {la la' : (k : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r}
      {P Q : FDSec X},
      P ∈ holSub X la →
        Q ∈ holSub X la' →
          P * Q ∈ holSub X (la + la') := by
  intro E _ _ _ r h5 Comp X la la' P Q hP hQ
  have key : ∀ (l : (k : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (R : FDSec X),
      R ∈ holSub X l → IsHolCusp X l R := by
    intro l R hR
    induction hR using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact fun c => (h5 r (X c) (l c) (l c) 0).1.1
    | add x y _ _ hx hy => exact fun c => (h5 r (X c) (l c) (l c) 0).1.2.1 _ (hx c) _ (hy c)
    | smul a x _ hx => exact fun c => (h5 r (X c) (l c) (l c) 0).1.2.2 a _ (hx c)
  exact Submodule.subset_span fun c =>
    (h5 r (X c) (la c) (la' c) 0).2.1 _ (key la P hP c) _ (key la' Q hQ c).1

end UpperTheory.Reformulated.B.Qe28
end
