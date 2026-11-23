module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CycOfPrime
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Real
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.SublatCount

section Abstract

variable {O N : Type} [CommRing O] [AddCommGroup N] [Module O N]

def Ker (I : Ideal O) (N : Type) [AddCommGroup N] [Module O N] : Set (Submodule O N) :=
  {L | ∃ f : N →ₗ[O] O ⧸ I, Function.Surjective f ∧ LinearMap.ker f = L}

theorem encard_eq_of_bijOn {α β : Type} {s : Set α} {t : Set β} {f : α → β} (h : Set.BijOn f s t) :
    s.encard = t.encard := by
  rw [← h.image_eq, h.injOn.encard_image]

theorem mem_ker_iff (I : Ideal O) (L : Submodule O N) :
    L ∈ Ker I N ↔ Nonempty ((N ⧸ L) ≃ₗ[O] (O ⧸ I)) := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f.quotKerEquivOfSurjective hf⟩
  · rintro ⟨e⟩
    refine ⟨e.toLinearMap ∘ₗ L.mkQ, e.surjective.comp L.mkQ_surjective, ?_⟩
    rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]

theorem smul_quot {I : Ideal O} {c : O} (hc : c ∈ I) (y : O ⧸ I) : c • y = 0 := by
  have : algebraMap O (O ⧸ I) c = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hc
  rw [Algebra.smul_def, this, zero_mul]

theorem smul_mem {I : Ideal O} {L : Submodule O N} (h : L ∈ Ker I N) {c : O} (hc : c ∈ I)
    (x : N) : c • x ∈ L := by
  obtain ⟨f, -, rfl⟩ := h
  rw [LinearMap.mem_ker, map_smul, smul_quot hc]

noncomputable def crt (I J : Ideal O) (h : IsCoprime I J) :
    (O ⧸ I * J) ≃ₗ[O] (O ⧸ I) × (O ⧸ J) :=
  { Ideal.quotientMulEquivQuotientProd I J h with
    map_smul' := fun c x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl }

theorem encard_mul (I J : Ideal O) (h : IsCoprime I J) :
    (Ker (I * J) N).encard = (Ker I N).encard * (Ker J N).encard := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  have key : ∀ {I J : Ideal O} {a b : O}, a ∈ I → b ∈ J → a + b = 1 →
      ∀ {L₁ L₂ L₁' L₂' : Submodule O N}, L₂ ∈ Ker J N → L₁' ∈ Ker I N →
      L₁ ⊓ L₂ = L₁' ⊓ L₂' → L₁ ≤ L₁' := by
    intro I J a b ha hb hab L₁ L₂ L₁' L₂' h2 h1' he x hx
    have h3 : b • x ∈ L₁ ⊓ L₂ := ⟨L₁.smul_mem b hx, smul_mem h2 hb x⟩
    rw [he] at h3
    have := L₁'.add_mem (smul_mem h1' ha x) h3.1
    rwa [← add_smul, hab, one_smul] at this
  rw [← Set.encard_prod]
  symm
  refine encard_eq_of_bijOn (f := fun p => p.1 ⊓ p.2) ⟨?_, ?_, ?_⟩
  · rintro ⟨_, _⟩ ⟨⟨f, hf, rfl⟩, ⟨g, hg, rfl⟩⟩
    refine ⟨(crt I J h).symm.toLinearMap ∘ₗ f.prod g, (crt I J h).symm.surjective.comp ?_, ?_⟩
    · rintro ⟨x, y⟩
      obtain ⟨u, rfl⟩ := hf x
      obtain ⟨v, rfl⟩ := hg y
      refine ⟨b • u + a • v, Prod.ext ?_ ?_⟩
      · change f (b • u + a • v) = f u
        rw [map_add (f := _), map_smul, map_smul, smul_quot ha, ← smul_quot ha (f u), ← add_smul,
          add_comm, hab, one_smul]
      · change g (b • u + a • v) = g v
        rw [map_add (f := _), map_smul, map_smul, smul_quot hb, ← smul_quot hb (g v), ← add_smul,
          add_comm, hab, one_smul]
    · rw [LinearEquiv.ker_comp, LinearMap.ker_prod]
  · rintro ⟨L₁, L₂⟩ ⟨h1, h2⟩ ⟨L₁', L₂'⟩ ⟨h1', h2'⟩ he
    have he : L₁ ⊓ L₂ = L₁' ⊓ L₂' := he
    have he' : L₂ ⊓ L₁ = L₂' ⊓ L₁' := by rw [inf_comm, he, inf_comm]
    have hba : b + a = 1 := by rw [add_comm, hab]
    exact Prod.ext (le_antisymm (key ha hb hab h2 h1' he) (key ha hb hab h2' h1 he.symm))
      (le_antisymm (key hb ha hba h1 h2' he') (key hb ha hba h1' h2 he'.symm))
  · rintro _ ⟨f, hf, rfl⟩
    let g := (crt I J h).toLinearMap ∘ₗ f
    have hg : Function.Surjective g := (crt I J h).surjective.comp hf
    refine ⟨(LinearMap.ker (LinearMap.fst O _ _ ∘ₗ g), LinearMap.ker (LinearMap.snd O _ _ ∘ₗ g)),
      ⟨⟨_, Prod.fst_surjective.comp hg, rfl⟩, ⟨_, Prod.snd_surjective.comp hg, rfl⟩⟩, ?_⟩
    change LinearMap.ker _ ⊓ LinearMap.ker _ = _
    rw [← LinearMap.ker_prod, ← LinearEquiv.ker_comp (crt I J h) f]
    rfl

theorem encard_top : (Ker (⊤ : Ideal O) N).encard = 1 := by
  rw [Set.encard_eq_one]
  refine ⟨⊤, Set.eq_singleton_iff_unique_mem.2 ⟨⟨0, fun y => ⟨0, Subsingleton.elim _ _⟩, by simp⟩, ?_⟩⟩
  intro L hL
  rw [eq_top_iff]
  intro x _
  simpa using smul_mem hL (c := 1) trivial x

theorem encard_max [IsDomain O] [Module.Finite O N] [Module.Projective O N] (P : Ideal O)
    [hP : P.IsMaximal] [Finite (O ⧸ P)] :
    (Ker P N).encard =
      ((∑ i ∈ Finset.range (Module.finrank O N), Nat.card (O ⧸ P) ^ i : ℕ) : ℕ∞) := by
  have : Nontrivial (O ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  have he : Ker P N = {L : Submodule O N | ∃ f : N →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = L} := by
    ext L
    refine exists_congr fun f => and_congr_left fun _ => ⟨fun hf h0 => ?_, fun hf y => ?_⟩
    · obtain ⟨v, hv⟩ := hf 1
      rw [h0] at hv
      exact zero_ne_one hv
    · obtain ⟨v, hv⟩ := GlobalTheory.SW.Hyper.surj_of_ne P f hf
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨c • v, by rw [map_smul, hv, Algebra.smul_def, mul_one]; rfl⟩
  obtain ⟨hf, hc⟩ := GlobalTheory.SW.Hyper.count (M := N) P
  rw [he, ← hf.cast_ncard_eq]
  congr 1
  have h1 : 1 < Nat.card (O ⧸ P) := Finite.one_lt_card
  refine Nat.eq_of_mul_eq_mul_right (m := Nat.card (O ⧸ P) - 1) (by omega) ?_
  rw [hc, geom_sum_mul_of_one_le h1.le]

theorem encard_prod [IsDomain O] [Module.Finite O N] [Module.Projective O N] (T : ℕ) (hT : T ≠ 0)
    (s : Finset (Ideal O)) (hs : ∀ P ∈ s, P.IsMaximal ∧ Nat.card (O ⧸ P) = T) :
    (Ker (∏ P ∈ s, P) N).encard =
      (((∑ i ∈ Finset.range (Module.finrank O N), T ^ i) ^ s.card : ℕ) : ℕ∞) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Ideal.one_eq_top, encard_top]; simp
  | insert P s hP ih =>
    obtain ⟨hm, hc⟩ := hs P (Finset.mem_insert_self _ _)
    have : Finite (O ⧸ P) := Nat.finite_of_card_ne_zero (hc ▸ hT)
    have hco : IsCoprime P (∏ Q ∈ s, Q) := IsCoprime.prod_right fun Q hQ =>
      Ideal.isCoprime_iff_sup_eq.2 (hm.coprime_of_ne (hs Q (Finset.mem_insert_of_mem hQ)).1
        fun h => hP (h ▸ hQ))
    rw [Finset.prod_insert hP, encard_mul _ _ hco, ih fun Q hQ => hs Q (Finset.mem_insert_of_mem hQ),
      encard_max, hc, Finset.card_insert_of_notMem hP, pow_succ', Nat.cast_mul]

end Abstract

theorem finrank_lattice {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V)
    (hM : Submodule.IsFullLattice K M) : Module.finrank (𝓞 K) M = Module.finrank K V := by
  letI := hM
  have hr : Module.rank (𝓞 K) V = Module.rank K V :=
    (IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl).symm
  have : Module.rank (𝓞 K) M = Module.rank K V := by
    apply le_antisymm
    · rw [← hr]; exact Submodule.rank_le M
    · obtain ⟨s, hsM, hspan, hli⟩ := exists_linearIndependent K (M : Set V)
      rw [Submodule.IsFullLattice.span_eq_top (A := K) (M := M)] at hspan
      have h1 : Module.rank K V = Cardinal.mk s := by
        rw [← rank_top, ← hspan, rank_span_set hli]
      have h2 : LinearIndependent (𝓞 K) (fun x : s => (⟨x.1, hsM x.2⟩ : M)) := by
        apply LinearIndependent.of_comp M.subtype
        exact (LinearIndependent.iff_fractionRing (𝓞 K) K).mpr hli
      rw [h1]
      exact h2.cardinal_le_rank
  simp only [Module.finrank, this]

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), Submodule.IsFullLattice K M → ∀ (T : ℕ) (s : Finset (Ideal (𝓞 K))), T.Prime → (∀ P ∈ s, P.IsMaximal ∧ Ideal.absNorm P = T) → {L : Submodule (𝓞 K) V | L ≤ M ∧ Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ P ∈ s, P))}.encard = (((∑ i ∈ Finset.range (Module.finrank K V), T ^ i) ^ s.card : ℕ) : ℕ∞) := by
  intro K V _ _ _ _ _ _ _ M hM T s hT hs
  letI := hM
  letI : Module.Finite (𝓞 K) M := Submodule.IsLattice.finite K M
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  rw [← finrank_lattice M hM, ← encard_prod (N := M) T hT.ne_zero s fun P hP =>
    ⟨(hs P hP).1, by rw [← (hs P hP).2, Ideal.absNorm_apply, Submodule.cardQuot_apply]⟩]
  refine encard_eq_of_bijOn (f := fun L => L.comap M.subtype) ⟨?_, ?_, ?_⟩
  · intro L hL
    exact (mem_ker_iff _ _).2 hL.2
  · intro L hL L' hL' h
    have := congrArg (Submodule.map M.subtype) h
    rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hL.1,
      inf_eq_right.2 hL'.1] at this
  · intro L hL
    have h : (L.map M.subtype).comap M.subtype = L := Submodule.comap_map_eq_of_injective M.injective_subtype L
    refine ⟨L.map M.subtype, ⟨Submodule.map_subtype_le _ _, ?_⟩, h⟩
    rw [h]
    exact (mem_ker_iff _ _).1 hL

end GlobalTheory.SublatCount
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.CovScal

theorem abs_det_mul_covolume_eq_nat_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (A B : Submodule ℤ E) [DiscreteTopology A] [IsZLattice ℝ A]
    [DiscreteTopology B] [IsZLattice ℝ B] (T : E →ₗ[ℝ] E) (hT : ∀ y ∈ A, T y ∈ B) :
    ∃ n : ℕ, |LinearMap.det T| * ZLattice.covolume A μ = n * ZLattice.covolume B μ := by
  classical

  let bA := Module.Free.chooseBasis ℤ A
  let bB := Module.Free.chooseBasis ℤ B
  let b₀ := bA.ofZLatticeBasis ℝ A
  let e := (bB.ofZLatticeBasis ℝ B).indexEquiv b₀
  let bB' := bB.reindex e
  let c := bB'.ofZLatticeBasis ℝ B
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ A) (Module.Free.ChooseBasisIndex ℤ A) ℤ :=
    fun i j => bB'.repr ⟨T (bA j), hT _ (bA j).2⟩ i
  have hb₀ : ((↑) : A → E) ∘ bA = b₀ := funext fun i => (bA.ofZLatticeBasis_apply ℝ A i).symm
  have hc : ((↑) : B → E) ∘ bB' = c := funext fun i => (bB'.ofZLatticeBasis_apply ℝ B i).symm

  have hM : c.toMatrix (T ∘ b₀) = M.map (Int.cast : ℤ → ℝ) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Matrix.map_apply, Function.comp_apply,
      show b₀ j = ((bA j : A) : E) from bA.ofZLatticeBasis_apply ℝ A j]
    exact bB'.ofZLatticeBasis_repr_apply ℝ B ⟨T (bA j), hT _ (bA j).2⟩ i
  have hdet : LinearMap.det T = b₀.det c * (M.det : ℝ) := by
    have h1 : b₀.det (T ∘ b₀) = LinearMap.det T := by
      rw [b₀.det_comp T b₀, b₀.det_self, mul_one]
    rw [← h1, b₀.det_apply, ← b₀.toMatrix_mul_toMatrix c (T ∘ b₀), Matrix.det_mul,
      ← b₀.det_apply, hM, Int.cast_det]
  have hcA := ZLattice.covolume_eq_det_mul_measureReal A μ bA b₀
  have hcB := ZLattice.covolume_eq_det_mul_measureReal B μ bB' b₀
  rw [hb₀, b₀.det_self, abs_one, one_mul] at hcA
  rw [hc] at hcB
  refine ⟨M.det.natAbs, ?_⟩
  rw [hcA, hcB, hdet, Nat.cast_natAbs, Int.cast_abs, abs_mul]
  ring

noncomputable def blockScal {ι : Type} (κ : Type) (d : ι → ℝ) : (ι → κ → ℝ) →ₗ[ℝ] (ι → κ → ℝ) :=
  LinearMap.pi fun v => (d v • (LinearMap.id : (κ → ℝ) →ₗ[ℝ] (κ → ℝ))).comp (LinearMap.proj v)

theorem blockScal_apply {ι κ : Type} (d : ι → ℝ) (y : ι → κ → ℝ) :
    blockScal κ d y = fun v i => d v * y v i := by
  funext v i
  simp [blockScal]

theorem det_blockScal {ι κ : Type} [Fintype ι] [Fintype κ] (d : ι → ℝ) :
    LinearMap.det (blockScal κ d) = ∏ v, d v ^ Fintype.card κ := by
  unfold blockScal
  rw [LinearMap.det_pi]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fintype_fun_eq_card]

theorem eq_one_of_forall_prime {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ p : ℕ, p.Prime → ∃ a b : ℕ, ¬ p ∣ a * b ∧ ρ ^ 2 * b = a) : ρ = 1 := by
  obtain ⟨a₀, b₀, h2, hab₀⟩ := h 2 Nat.prime_two
  have ha₀ : a₀ ≠ 0 := by rintro rfl; simp at h2
  have hb₀ : b₀ ≠ 0 := by rintro rfl; simp at h2

  have key : a₀ = b₀ := by
    refine Nat.eq_of_factorization_eq ha₀ hb₀ fun p => ?_
    by_cases hp : p.Prime
    · obtain ⟨a, b, hp', hab⟩ := h p hp
      have ha : a ≠ 0 := by rintro rfl; simp at hp'
      have hb : b ≠ 0 := by rintro rfl; simp at hp'
      have hcast : ((a₀ * b : ℕ) : ℝ) = ((a * b₀ : ℕ) : ℝ) := by
        push_cast
        rw [← hab₀, ← hab]
        ring
      have hnat : a₀ * b = a * b₀ := by exact_mod_cast hcast
      have hpa : a.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd fun hd => hp' (dvd_mul_of_dvd_left hd b)
      have hpb : b.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd fun hd => hp' (dvd_mul_of_dvd_right hd a)
      have hf := congrArg (fun n => n.factorization p) hnat
      simp only [Nat.factorization_mul ha₀ hb, Nat.factorization_mul ha hb₀, Finsupp.add_apply,
        hpa, hpb] at hf
      omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  rw [key] at hab₀
  have hb₀' : (b₀ : ℝ) ≠ 0 := by exact_mod_cast hb₀
  have hsq : ρ ^ 2 = 1 := mul_right_cancel₀ hb₀' (by rw [hab₀, one_mul])
  have hfac : (ρ - 1) * (ρ + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h' | h' <;> linarith

theorem covolume_eq_of_scalars : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (A B : Submodule ℤ (ι → κ → ℝ)) [DiscreteTopology A] [IsZLattice ℝ A] [DiscreteTopology B] [IsZLattice ℝ B], (∀ p : ℕ, p.Prime → ∃ (d : ι → ℝ) (N : ℕ), ¬ p ∣ N ∧ ∏ v, d v ^ 2 = N ∧ (∀ y ∈ A, (fun v i => d v * y v i) ∈ B) ∧ ∀ y ∈ B, (fun v i => d v * y v i) ∈ A) → ZLattice.covolume A volume = ZLattice.covolume B volume := by
  intro ι κ _ _ A B _ _ _ _ h
  have hA : 0 < ZLattice.covolume A volume := ZLattice.covolume_pos A volume
  have hB : 0 < ZLattice.covolume B volume := ZLattice.covolume_pos B volume
  set cA := ZLattice.covolume A volume
  set cB := ZLattice.covolume B volume
  suffices key : cA / cB = 1 from (div_eq_one_iff_eq hB.ne').mp key
  refine eq_one_of_forall_prime (div_pos hA hB) fun p hp => ?_
  obtain ⟨d, N, hpN, hN, hAB, hBA⟩ := h p hp
  have hT : ∀ y ∈ A, blockScal κ d y ∈ B := fun y hy => by rw [blockScal_apply]; exact hAB y hy
  have hT' : ∀ y ∈ B, blockScal κ d y ∈ A := fun y hy => by rw [blockScal_apply]; exact hBA y hy
  obtain ⟨n, hn⟩ := abs_det_mul_covolume_eq_nat_mul volume A B (blockScal κ d) hT
  obtain ⟨m, hm⟩ := abs_det_mul_covolume_eq_nat_mul volume B A (blockScal κ d) hT'
  set D := |LinearMap.det (blockScal κ d)|

  have hD2 : D ^ 2 = (N : ℝ) ^ Fintype.card κ := by
    rw [sq_abs, det_blockScal, ← hN, Finset.prod_pow, Finset.prod_pow]
    ring
  have hnm : ((n * m : ℕ) : ℝ) = ((N ^ Fintype.card κ : ℕ) : ℝ) := by
    push_cast
    have h0 : ((n : ℝ) * m - D ^ 2) * (cA * cB) = 0 := by
      linear_combination (-(D * cB)) * hn - (n * cB) * hm
    rcases mul_eq_zero.mp h0 with h0 | h0
    · rw [← hD2]; linarith
    · exact absurd h0 (mul_pos hA hB).ne'
  have hnat : n * m = N ^ Fintype.card κ := by exact_mod_cast hnm
  refine ⟨n, m, ?_, ?_⟩
  · rw [hnat]
    exact fun hd => hpN (hp.dvd_of_dvd_pow hd)
  · rw [div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hB.ne')]
    linear_combination (-cA) * hm + cB * hn

end GlobalTheory.CovScal
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem exists_dual_of_anisotropic_orthogonal (E : Type) [Field E] [StarRing E] (n m : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin m) (Fin m) E) (x : Fin n → E)
    (A : Matrix (Fin n) (Fin m) E) (hn : m + 1 = n) (hJ : Jᴴ = J) (hdet : J'.det ≠ 0)
    (hβ : star x ⬝ᵥ (J *ᵥ x) ≠ 0) (hx : star x ᵥ* (J * A) = 0) (hA : Aᴴ * J * A = J') :
    ∃ (u : Fin n → E) (A' : Matrix (Fin m) (Fin n) E), A' * A = 1 ∧ A' *ᵥ x = 0 ∧
      u ᵥ* A = 0 ∧ u ⬝ᵥ x = 1 ∧ vecMulVec x u + A * A' = 1 ∧ Aᴴ *ᵥ (J *ᵥ x) = 0 := by
  have h6 : Aᴴ *ᵥ (J *ᵥ x) = 0 := by
    have := congrArg star hx
    rw [Matrix.star_vecMul, star_star, Matrix.conjTranspose_mul, hJ, star_zero,
      ← Matrix.mulVec_mulVec] at this
    exact this
  obtain ⟨u, hu⟩ : ∃ u : Fin n → E, u = (star x ⬝ᵥ (J *ᵥ x))⁻¹ • (star x ᵥ* J) := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ A' : Matrix (Fin m) (Fin n) E, A' = J'⁻¹ * Aᴴ * J := ⟨_, rfl⟩
  have h1 : A' * A = 1 := by
    rw [hA', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA]
    exact Matrix.nonsing_inv_mul _ (Ne.isUnit hdet)
  have h2 : A' *ᵥ x = 0 := by
    rw [hA', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h6, Matrix.mulVec_zero]
  have h3 : u ᵥ* A = 0 := by
    rw [hu, Matrix.smul_vecMul, Matrix.vecMul_vecMul, hx, smul_zero]
  have h4 : u ⬝ᵥ x = 1 := by
    rw [hu, smul_dotProduct, ← Matrix.dotProduct_mulVec, smul_eq_mul, inv_mul_cancel₀ hβ]
  refine ⟨u, A', h1, h2, h3, h4, ?_, h6⟩
  subst hn
  let C : Matrix (Fin (m + 1)) (Fin (m + 1)) E :=
    Matrix.of fun i j => (Fin.cons (x i) (fun k => A i k) : Fin (m + 1) → E) j
  let C' : Matrix (Fin (m + 1)) (Fin (m + 1)) E :=
    Matrix.of fun i j => (Fin.cons (u j) (fun k => A' k j) : Fin (m + 1) → E) i
  have hCC : C' * C = 1 := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa [C, C', Matrix.mul_apply, dotProduct] using h4
    · have := congrFun h3 j
      simpa [C, C', Matrix.mul_apply, dotProduct, Matrix.vecMul, (Fin.succ_ne_zero j).symm] using this
    · have := congrFun h2 i
      simpa [C, C', Matrix.mul_apply, dotProduct, Matrix.mulVec, Fin.succ_ne_zero i] using this
    · have := congrFun (congrFun h1 i) j
      simpa [C, C', Matrix.mul_apply, Matrix.one_apply] using this
  have hCC' : C * C' = 1 := mul_eq_one_comm.mp hCC
  rw [← hCC']
  ext i j
  simp [C, C', Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMulVec_apply]

end GlobalTheory.StabUnfold
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem right_inv_eq_smul_left_inv :
    ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (K : Set G) (μ ν : Measure G) [SFinite μ] [SFinite ν], μ Kᶜ = 0 → ν Kᶜ = 0 → μ Set.univ = 1 → (∀ k ∈ K, μ.map (fun g => k * g) = μ) → (∀ k ∈ K, ν.map (fun g => g * k) = ν) → ν = ν Set.univ • μ := by
  intro G _ _ _ K μ ν _ _ hμK hνK hμ1 hμinv hνinv
  ext A hA

  have hS : MeasurableSet {p : G × G | p.1 * p.2 ∈ A} := measurable_mul hA
  have hμae : ∀ᵐ g ∂μ, g ∈ K := by
    rw [ae_iff]
    exact hμK
  have hνae : ∀ᵐ g ∂ν, g ∈ K := by
    rw [ae_iff]
    exact hνK
  have h1 : (ν.prod μ) {p : G × G | p.1 * p.2 ∈ A} = ν Set.univ * μ A := by
    rw [Measure.prod_apply hS]
    have hc : ∀ᵐ h ∂ν, μ (Prod.mk h ⁻¹' {p : G × G | p.1 * p.2 ∈ A}) = μ A := by
      filter_upwards [hνae] with h hh
      show μ ((fun g => h * g) ⁻¹' A) = μ A
      rw [← Measure.map_apply (measurable_const_mul h) hA, hμinv h hh]
    rw [lintegral_congr_ae hc, lintegral_const, mul_comm]
  have h2 : (ν.prod μ) {p : G × G | p.1 * p.2 ∈ A} = ν A := by
    rw [Measure.prod_apply_symm hS]
    have hc : ∀ᵐ g ∂μ, ν ((fun h => (h, g)) ⁻¹' {p : G × G | p.1 * p.2 ∈ A}) = ν A := by
      filter_upwards [hμae] with g hg
      show ν ((fun h => h * g) ⁻¹' A) = ν A
      rw [← Measure.map_apply (measurable_mul_const g) hA, hνinv g hg]
    rw [lintegral_congr_ae hc, lintegral_const, hμ1, mul_one]
  rw [Measure.smul_apply, smul_eq_mul, ← h1, h2]

end GlobalTheory.IwConst
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.tendsto_small_ball_density_of_squeeze : ∀ (f : ℝ → ENNReal) (d : ℕ) (v : ENNReal), v ≠ ⊤ → (∀ η : ℝ, 0 < η → ∃ b : ℝ → ENNReal, Filter.Tendsto (fun r : ℝ => b r / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds v) ∧ ∀ᶠ r in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), b (r / (1 + η)) ≤ ENNReal.ofReal (1 + η) * f r ∧ f r ≤ ENNReal.ofReal (1 + η) * b ((1 + η) * r)) → Filter.Tendsto (fun r : ℝ => f r / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds v) := by
  first | exact @GlobalTheory.IwConst.tendsto_div_pow_of_squeeze | exact GlobalTheory.IwConst.tendsto_div_pow_of_squeeze | (intros; apply GlobalTheory.IwConst.tendsto_div_pow_of_squeeze <;> assumption)
end
