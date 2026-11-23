module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.StCoiLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCorner
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.IdemNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle009
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem hr_span {A F : Type} [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F] {n a : ℕ}
    (t : A) (ht : t ≠ 0) (T : Set (Matrix (Fin n) (Fin n) A))
    (hT : ∀ Z ∈ Ev A A n a, ∃ s : ℕ, t ^ s • Z ∈ Submodule.span A T)
    (S : Submodule F (Matrix (Fin n) (Fin n) F)) (hS : ∀ Y ∈ T, Y.map (algebraMap A F) ∈ S) :
    Ev F F n a ≤ S := by
  have h1 : ∀ Y ∈ Submodule.span A T, Y.map (algebraMap A F) ∈ S := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem y hy => exact hS y hy
    | zero => simp
    | add y z _ _ hy hz =>
      have : (y + z).map (algebraMap A F) = y.map (algebraMap A F) + z.map (algebraMap A F) := by
        ext i j; simp
      rw [this]; exact S.add_mem hy hz
    | smul c y _ hy =>
      have : (c • y).map (algebraMap A F) = algebraMap A F c • y.map (algebraMap A F) := by
        ext i j; simp
      rw [this]; exact S.smul_mem _ hy
  intro Z hZ
  have hZ' : Z = ∑ i, ∑ j, single i j (Z i j) := matrix_eq_sum_single Z
  rw [hZ']
  refine S.sum_mem fun i _ => S.sum_mem fun j _ => ?_
  by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
  · obtain ⟨s, hs⟩ := hT (single i j 1) (fun p q => ⟨fun _ => trivial, fun e' => by
      rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact e' e⟩)
    have h2 := S.smul_mem (Z i j * (algebraMap A F (t ^ s))⁻¹) (h1 _ hs)
    have hne : algebraMap A F (t ^ s) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A F)]
      exact pow_ne_zero _ ht
    convert h2 using 1
    ext p q
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one, mul_assoc, inv_mul_cancel₀ hne, mul_one]
    · simp
  · have : Z i j = 0 := (hZ i j).2 e
    simp [this]

theorem UpperTheory.V.Pa.hat_range :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)], Function.Surjective (algebraMap Bh (FractionRing x.A)) → ∀ H : Hat h x u.D P.ker Bh (G.frame.eps O B), ∀ Z, Z ∈ Ev (FractionRing x.A) (FractionRing x.A) n x.a ↔ ∃ y, H.r y = Z := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hs H Z
  have hsm : ∀ (b : Bh) (Y : Matrix (Fin n) (Fin n) (FractionRing x.A)),
      b • Y = algebraMap Bh (FractionRing x.A) b • Y := by
    intro b Y
    ext i j
    simp [Algebra.smul_def]
  constructor
  · let S : Submodule (FractionRing x.A) (Matrix (Fin n) (Fin n) (FractionRing x.A)) :=
      { carrier := {Z | ∃ y, H.r y = Z}
        add_mem' := by
          rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩
          exact ⟨y + z, map_add _ _ _⟩
        zero_mem' := ⟨0, map_zero _⟩
        smul_mem' := by
          rintro c _ ⟨y, rfl⟩
          obtain ⟨b, rfl⟩ := hs c
          exact ⟨b • y, by rw [map_smul, hsm]⟩ }
    intro hZ
    refine hr_span (A := x.A) x.t PowerSeries.X_ne_zero _ x.span S ?_ hZ
    rintro _ ⟨g, -, rfl⟩
    obtain ⟨g', hg'⟩ := h.surj g.1
    have hm : g' ∈ G.η.ker := by
      have h1 := h.η g'
      rw [hg'] at h1
      rw [MonoidHom.mem_ker, ← h1]
      exact g.2
    have : h.p₀ ⟨g', hm⟩ = g := Subtype.ext hg'
    exact ⟨_, by rw [← this]; exact H.r_ι ⟨g', hm⟩⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := H.surj y
    induction z using MonoidAlgebra.induction_on with
    | of g =>
      have := H.r_ι g
      rw [MonoidAlgebra.of_apply, this]
      intro i j
      refine ⟨fun _ => trivial, fun e => ?_⟩
      have h0 : mat x.ρ (h.p₀ g) i j = 0 := (x.blk (h.p₀ g) i j).2 e
      rw [Submodule.mem_bot, Matrix.map_apply, h0, map_zero]
    | add f g hf hg =>
      rw [map_add (f := _), map_add (f := _)]
      exact Submodule.add_mem _ hf hg
    | smul b f hf =>
      rw [map_smul, map_smul, hsm]
      exact Submodule.smul_mem _ _ hf
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem oB_lt {n a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ n) (i : Fin n) :
    ((oB n a i : Fin n) : ℕ) < a ↔ (i : ℕ) < a := by
  unfold oB
  split_ifs with hi
  · simp only [hi, iff_true]
    exact h1
  · simp only [hi, iff_false, not_lt]
    have := i.2
    omega

private theorem oB_oB {n a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ n) (i : Fin n) : oB n a (oB n a i) = oB n a i := by
  have key := oB_lt h1 h2 i
  unfold oB at key ⊢
  by_cases hi : (i : ℕ) < a
  · have : ((if (i : ℕ) < a then (⟨0, by omega⟩ : Fin n) else ⟨n - 1, by omega⟩ : Fin n) : ℕ) < a := key.2 hi
    simp only [hi, if_true] at this ⊢
    simp only [this, if_true]
  · have : ¬ ((if (i : ℕ) < a then (⟨0, by omega⟩ : Fin n) else ⟨n - 1, by omega⟩ : Fin n) : ℕ) < a :=
      fun h => hi (key.1 h)
    simp only [hi, if_false] at this ⊢
    simp only [this, if_false]

private theorem single_mem {F : Type} [Field F] {n a : ℕ} (p q : Fin n) (h : (p : ℕ) < a ↔ (q : ℕ) < a) :
    (single p q 1 : Matrix (Fin n) (Fin n) F) ∈ Ev F F n a := by
  intro i j
  refine ⟨fun _ => Submodule.mem_top, fun hij => ?_⟩
  rw [Matrix.single_apply]
  split_ifs with hpq
  · obtain ⟨rfl, rfl⟩ := hpq
    exact absurd h hij
  · exact Submodule.zero_mem _

theorem UpperTheory.V.Pa.idem :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Module.Finite B E] (a : ℕ) (D : Det n B E) (T : TrInv B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F), 1 ≤ a → a ≤ n → IsUnit (2 : B) → D.IsCH → (∀ y, T.tr y = D.tr y) → RingHom.ker (algebraMap B F) = maximalIdeal B → (∀ y, (D.chi y).map (algebraMap B F) = (r y).charpoly) → (∀ y, r (T.st y) = (r y)ᵀ) → (∀ Z ∈ Ev F F n a, ∃ y, r y = Z) → ∃ U : T.Units (Fin n) (oB n a), (∀ i, r (U.x i) = single (oB n a i) i 1) ∧ ∀ i, D.D B[X] (1 + X ⊗ₜ U.ep i) = 1 + X := by
  intro B E F _ _ _ _ _ _ n _ _ _ a D T r h1 h2 h2u hCH htr hker hchi hst hsurj
  have hn : 1 ≤ n := le_trans h1 h2
  haveI : IsAdicComplete (maximalIdeal B) E := GlobalTheory.isAdicComplete_of_finite (maximalIdeal B) E
  obtain ⟨hnil, hidem⟩ := idem_nil D r hCH hker hchi
  have hdiag : ∀ i : Fin n, ∃ y, r y = single i i 1 := fun i =>
    hsurj _ (single_mem i i Iff.rfl)
  obtain ⟨ep, hcoi, hstep, hrep⟩ :=
    st_coi_lift T (maximalIdeal B) r h2u (le_of_eq hker.symm) hnil hst hdiag
  have hD : ∀ i, D.D B[X] (1 + X ⊗ₜ ep i) = 1 + X := fun i =>
    hidem (ep i) i (hcoi.idem i) (hrep i)
  have hcorner := fun i => d_corner D (ep i) hCH (hcoi.idem i) (hD i) hn
  haveI : HenselianRing B (RingHom.ker (algebraMap B F)) := by
    rw [hker]
    infer_instance
  obtain ⟨U, hUep, hUx⟩ := units_exist T (oB n a) r ep h2u (fun i => oB_oB h1 h2 i) hst
    (fun i => hsurj _ (single_mem _ _ (oB_lt h1 h2 i))) hcoi hstep hrep
    (fun i => by rw [htr]; exact (hcorner i).2.1)
    (fun i y => ⟨D.tr (ep i * y), (hcorner i).1 y⟩)
  refine ⟨U, hUx, fun i => ?_⟩
  rw [hUep]
  exact hD i
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.gr_ss :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} {a : ℕ} {T : TrInv B E} {r : E →ₐ[B] Matrix (Fin n) (Fin n) F} {ep : Fin n → E} (g : GrAlg T n a r ep) (κ : Type) [Field κ] [Algebra B κ] (s : B), algebraMap B κ s ≠ 0 → s ∈ Module.annihilator B g.N → IsSemisimpleRing (κ ⊗[B] E) := by
  intro B E F _ _ _ _ _ _ n a T r ep g κ _ _ s hs hann
  classical
  let M : Fin n → Fin n → Matrix (Fin n) (Fin n) g.AA :=
    fun i k => Matrix.single i k (if ((i : ℕ) < a ↔ (k : ℕ) < a) then 1 else 0)
  have hM : ∀ i k, ∃ x : E, g.φ x = M i k := by
    intro i k
    rw [← Set.mem_range, g.range]
    intro p q
    refine ⟨fun _ => ?_, fun hpq => ?_⟩
    · simp only [M, Matrix.single_apply]
      split_ifs
      · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      · exact zero_mem _
      · exact zero_mem _
    · simp only [M, Matrix.single_apply]
      split_ifs with h1 h2
      · obtain ⟨rfl, rfl⟩ := h1
        exact absurd h2 hpq
      · exact zero_mem _
      · exact zero_mem _
  choose e he using hM
  have hmul : ∀ i k l : Fin n, ((i : ℕ) < a ↔ (k : ℕ) < a) → ((k : ℕ) < a ↔ (l : ℕ) < a) →
      e i k * e k l = e i l := by
    intro i k l hik hkl
    apply g.φ_inj
    rw [map_mul, he, he, he]
    simp only [M, if_pos hik, if_pos hkl, if_pos (hik.trans hkl), Matrix.single_mul_single_same,
      mul_one]
  have hzero : ∀ i k l m : Fin n, k ≠ l → e i k * e l m = 0 := by
    intro i k l m hkl
    apply g.φ_inj
    rw [map_mul, he, he, map_zero]
    exact Matrix.single_mul_single_of_ne _ _ _ _ hkl _
  have hcross : ∀ i k : Fin n, ¬((i : ℕ) < a ↔ (k : ℕ) < a) → e i k = 0 := by
    intro i k hik
    apply g.φ_inj
    rw [he, map_zero]
    simp only [M, if_neg hik, Matrix.single_zero]
  have hsum : ∑ i, e i i = 1 := by
    apply g.φ_inj

    rw [map_sum, map_one]
    simp only [he, M, iff_self, if_true]
    ext p q
    rw [Matrix.sum_apply]
    simp only [Matrix.single_apply]
    by_cases hpq : p = q
    · subst hpq
      simp
    · rw [Matrix.one_apply_ne hpq]
      exact Finset.sum_eq_zero (fun x _ => if_neg (fun h => hpq (h.1.symm.trans h.2)))
  have hdec : ∀ y : E, ∃ b : Fin n → Fin n → B, s • y = ∑ i, ∑ k, b i k • e i k := by
    intro y
    have hent : ∀ i k, ∃ c : B, s • g.φ y i k = c • (if ((i : ℕ) < a ↔ (k : ℕ) < a) then 1 else 0) := by
      intro i k
      obtain ⟨h1, h2⟩ := (g.range (g.φ y)).mp ⟨y, rfl⟩ i k
      by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
      · obtain ⟨c, hc⟩ := Submodule.mem_one.mp (h1 hik)
        refine ⟨s * c, ?_⟩
        rw [if_pos hik, ← hc, Algebra.algebraMap_eq_smul_one, smul_smul]
      · refine ⟨0, ?_⟩
        rw [if_neg hik, smul_zero]
        have := (Module.mem_annihilator.mp hann) ⟨_, h2 hik⟩
        simpa using congrArg Subtype.val this
    choose c hc using hent
    refine ⟨c, g.φ_inj ?_⟩

    rw [map_smul, map_sum]
    ext p q

    simp only [map_sum, map_smul, he, M, Matrix.smul_apply, Matrix.sum_apply, Matrix.single_apply]
    rw [hc, Finset.sum_eq_single p (fun i _ hi => Finset.sum_eq_zero (fun k _ => by
        rw [if_neg (fun h => hi h.1), smul_zero])) (by simp),
      Finset.sum_eq_single q (fun k _ hk => by rw [if_neg (fun h => hk h.2), smul_zero]) (by simp)]
    simp
  let bf : Fin n → Bool := fun i => decide ((i : ℕ) < a)
  let cl : Fin n → Set.range bf := Set.rangeFactorization bf
  have hcl : ∀ i k : Fin n, cl i = cl k ↔ ((i : ℕ) < a ↔ (k : ℕ) < a) := by
    intro i k
    simp only [cl, bf, Set.rangeFactorization, Subtype.mk.injEq, decide_eq_decide]
  let d : Set.range bf → Type := fun t => {i : Fin n // cl i = t}
  haveI : ∀ t, Nonempty (d t) := fun t => by
    obtain ⟨i, hi⟩ := Set.rangeFactorization_surjective t
    exact ⟨⟨i, hi⟩⟩
  let ee : (t : Set.range bf) → d t → d t → κ ⊗[B] E := fun t i k => (1 : κ) ⊗ₜ[B] e i.1 k.1
  obtain ⟨j, hj⟩ := alghom_of_units (K := κ) (E := κ ⊗[B] E) d ee
    (fun t i k l => by
      simp only [ee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hmul _ _ _ ((hcl _ _).mp (i.2.trans k.2.symm)) ((hcl _ _).mp (k.2.trans l.2.symm))])
    (fun t i k l m hkl => by
      simp only [ee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hzero _ _ _ _ (fun h => hkl (Subtype.ext h)), TensorProduct.tmul_zero])
    (fun t u i k l m htu => by
      simp only [ee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hzero _ _ _ _ (fun h => htu (by rw [← k.2, ← l.2, h])), TensorProduct.tmul_zero])
    (by
      simp only [ee]
      rw [Fintype.sum_fiberwise cl (fun i => (1 : κ) ⊗ₜ[B] e i i), ← TensorProduct.tmul_sum, hsum,
        Algebra.TensorProduct.one_def])
  have hgen : ∀ i k : Fin n, (1 : κ) ⊗ₜ[B] e i k ∈ j.range := by
    intro i k
    by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · have hk : cl k = cl i := (hcl k i).mpr hik.symm
      exact (AlgHom.mem_range j).mpr
        ⟨Pi.single (cl i) (Matrix.single ⟨i, rfl⟩ ⟨k, hk⟩ 1), hj (cl i) ⟨i, rfl⟩ ⟨k, hk⟩⟩
    · rw [hcross i k hik, TensorProduct.tmul_zero]
      exact Subalgebra.zero_mem _
  have hone : ∀ y : E, (1 : κ) ⊗ₜ[B] y ∈ j.range := by
    intro y
    obtain ⟨b, hb⟩ := hdec y
    have h1 : (1 : κ) ⊗ₜ[B] y = (algebraMap B κ s)⁻¹ • ((1 : κ) ⊗ₜ[B] (s • y)) := by
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one,
        smul_eq_mul, inv_mul_cancel₀ hs]
    rw [h1, hb, TensorProduct.tmul_sum]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ (fun i _ => ?_)) _
    rw [TensorProduct.tmul_sum]
    refine Subalgebra.sum_mem _ (fun k _ => ?_)
    have h2 : (1 : κ) ⊗ₜ[B] (b i k • e i k) = (algebraMap B κ (b i k)) • ((1 : κ) ⊗ₜ[B] e i k) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    rw [h2]
    exact Subalgebra.smul_mem _ (hgen i k) _
  refine RingHom.isSemisimpleRing_of_surjective j.toRingHom ?_
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul u y =>
    obtain ⟨z, hz⟩ := (AlgHom.mem_range j).mp (hone y)
    refine ⟨u • z, ?_⟩
    show j (u • z) = _
    rw [map_smul, hz, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy =>
    obtain ⟨z, hz⟩ := hx
    obtain ⟨w, hw⟩ := hy
    exact ⟨z + w, by rw [map_add (f := _), hz, hw]⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.gr_I :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} (T : TrInv B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F) (U : T.Units (Fin n) (oB n n)), 1 ≤ n → (∀ y, r (T.st y) = (r y)ᵀ) → (∀ i, r (U.x i) = single (oB n n i) i 1) → Nonempty (GrAlg T n n r U.ep) := by
  intro B E F _ _ _ _ _ _ n T r U hn hr hx
  have ho : ∀ i : Fin n, oB n n i = ⟨0, by omega⟩ := fun i => Fin.ext (by simp [oB, i.isLt])
  obtain ⟨φ, hφ, hst, -⟩ := units_one_block T (oB n n) U ⟨0, by omega⟩ ho
  have hU := units_basic T (oB n n) U
  have hxe : ∀ i' i : Fin n, U.x i' * U.ep i = if i' = i then U.x i' else 0 := by
    intro i' i
    conv_lhs => rw [← U.x_mem i']
    split_ifs with h
    · subst h
      rw [mul_assoc, (U.coi.idem i').eq, U.x_mem]
    · rw [mul_assoc, U.coi.ortho h, mul_zero]
  have hone : (1 : Submodule B B) = ⊤ :=
    eq_top_iff.2 fun x _ => Submodule.mem_one.2 ⟨x, rfl⟩
  refine ⟨@GrAlg.mk B E F _ _ _ _ _ _ T n n r U.ep B _ _ inferInstance (fun a b h => h) ⊥
    ?_ ?_ (fun _ => rfl) φ.toAlgHom φ.injective ?_ hst ?_ ?_⟩
  · rw [hone]
    exact isCompl_top_bot
  · intro y hy z hz
    rw [Submodule.mem_bot] at hy
    subst hy
    exact ⟨0, zero_mem _, by simp⟩
  · intro Y
    constructor
    · intro _
      intro i j
      refine ⟨fun _ => by rw [hone]; trivial, fun h => absurd ⟨fun _ => j.isLt, fun _ => i.isLt⟩ h⟩
    · intro _
      exact φ.surjective Y
  · intro i
    show φ (U.ep i) = _
    ext i' j'
    rw [hφ, hxe]
    split_ifs with h1
    · subst h1
      by_cases h2 : i' = j'
      · subst h2
        rw [U.x_st, U.tr_ep]
        simp [Matrix.single_apply]
      · rw [hU.1 i' j' h2, map_zero]
        simp [Matrix.single_apply, h2, Ne.symm h2]
    · simp [Matrix.single_apply, Ne.symm h1]
  · intro y i j b h
    rw [Submodule.mem_bot, sub_eq_zero] at h
    change φ y i j = b at h
    rw [← h, hφ]
    have he0 : r (U.ep ⟨0, by omega⟩) = single ⟨0, by omega⟩ ⟨0, by omega⟩ 1 := by
      have h0 := U.x_base ⟨0, by omega⟩
      rw [ho] at h0
      rw [← h0, hx, ho]
    have hk := hU.2.2.2.2.1 i j y (by rw [ho, ho])
    have hr2 := congrArg (fun M => M ⟨0, by omega⟩ ⟨0, by omega⟩) (congrArg r hk)
    simp only [map_mul, map_smul, hr, hx, ho, he0] at hr2
    simp [Matrix.mul_apply, Matrix.single_apply, Algebra.smul_def] at hr2
    rw [hr2]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem characteristic_polynomial_compatibility {n : ℕ} {G B A Bh F E : Type} [Group G] [CommRing B] [CommRing A] [CommRing Bh] [CommRing F]
    [Ring E] [Algebra Bh E] [Algebra Bh F] (D : GDet n B G) (f : B →+* A) (g : B →+* Bh) (a : A →+* F)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (hD : D.map f = GDet.ofRep ρ)
    (hc : ∀ b, algebraMap Bh F (g b) = a (f b)) (ι : MonoidAlgebra Bh G →ₐ[Bh] E) (DE : Det n Bh E)
    (hp : DE.pull ι = (D.map g).toDet) (r : E →ₐ[Bh] Matrix (Fin n) (Fin n) F)
    (hr : ∀ s, r (ι (MonoidAlgebra.single s 1)) = (ρ s).map a) (z : MonoidAlgebra Bh G) :
    (DE.chi (ι z)).map (algebraMap Bh F) = (r (ι z)).charpoly := by
  have hc' : (algebraMap Bh F).comp g = a.comp f := RingHom.ext hc
  rw [← (d_pull DE ι).1 z, hp, (d_toDet _ z).1, ← ((d_gmap (D.map g)).2.2.1 (algebraMap Bh F) z).1,
    (d_gmap D).2.1, hc', ← (d_gmap D).2.1, hD, (d_gmap (GDet.ofRep ρ)).2.2.2, ← (d_toDet _ _).1,
    d_toDet_ofRep.1, (d_ofRep _ _ _).1]
  congr 1
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | single s b =>
    have : (MonoidAlgebra.single s b : MonoidAlgebra Bh G) = b • MonoidAlgebra.single s 1 := by simp
    rw [MonoidAlgebra.mapRingHom_single]
    conv_rhs => rw [this, map_smul, map_smul, hr]
    ext i j
    simp [GDet.repAlg, Algebra.smul_def]

theorem UpperTheory.V.Pa.hat_chi :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)], (∀ b, algebraMap Bh (FractionRing x.A) (algebraMap B Bh b) = algebraMap x.A (FractionRing x.A) (P.f b)) → ∀ H : Hat h x u.D P.ker Bh (G.frame.eps O B), ∀ y, (H.DE.chi y).map (algebraMap Bh (FractionRing x.A)) = (H.r y).charpoly := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hc H y
  obtain ⟨z, rfl⟩ := H.surj y
  exact characteristic_polynomial_compatibility u.D P.f.toRingHom (algebraMap B Bh) (algebraMap x.A (FractionRing x.A)) (mat (x.ρ.comp h.p₀))
    P.maps.1 hc H.ι H.DE H.pull H.r H.r_ι z
end
