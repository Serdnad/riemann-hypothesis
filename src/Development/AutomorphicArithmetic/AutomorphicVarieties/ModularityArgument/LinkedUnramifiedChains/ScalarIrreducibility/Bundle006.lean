module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle030
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.ExistsBetweenFinset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DerCont
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem chev_prime (B A : Type) [CommRing B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A]
    (P : Ideal A) [P.IsPrime] (a : A) (ha : a ∉ P) :
    ∃ b : B, b ∉ P.comap (algebraMap B A) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K),
      P.comap (algebraMap B A) ≤ RingHom.ker y → y b ≠ 0 →
        ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 ∧ P ≤ RingHom.ker ξ := by
  set p := P.comap (algebraMap B A)
  haveI : Algebra.FiniteType B (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ B P) (Ideal.Quotient.mkₐ_surjective B P)
  haveI : Algebra.FiniteType (B ⧸ p) (A ⧸ P) :=
    Algebra.FiniteType.of_restrictScalars_finiteType B (B ⧸ p) (A ⧸ P)
  obtain ⟨b', hb'0, hb'⟩ := UpperTheory.V.J.chev (B ⧸ p) (A ⧸ P) Ideal.algebraMap_quotient_injective
    (Ideal.Quotient.mk P a) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  refine ⟨b, ?_, ?_⟩
  · rwa [Ne, Ideal.Quotient.eq_zero_iff_mem] at hb'0
  · intro K _ _ y hy hyb
    let y' : B ⧸ p →+* K := Ideal.Quotient.lift p y (fun x hx => (RingHom.mem_ker).mp (hy hx))
    obtain ⟨ξ', hξ'1, hξ'2⟩ := hb' K y' (by simpa [y'] using hyb)
    refine ⟨ξ'.comp (Ideal.Quotient.mk P), ?_, hξ'2, ?_⟩
    · ext x
      have h := congrArg (fun f => f (Ideal.Quotient.mk p x)) hξ'1
      simp only [RingHom.comp_apply, y', Ideal.Quotient.lift_mk] at h ⊢
      exact h
    · intro x hx
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

private theorem gen_out {R : Type} [CommRing R] {s : Set R} {P : Ideal R} (h : ¬ Ideal.span s ≤ P) :
    ∃ x ∈ s, x ∉ P := by
  by_contra hc
  push_neg at hc
  exact h (Ideal.span_le.2 hc)

set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.J.genPt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ (P : Ideal S.A) (Gd : (S.B →ₐ[c.O] Qbar l) → Prop), P ∈ minimalPrimes S.A → S.u.TI P →
          (∀ b ∉ S.π P, ∃ y : S.B →ₐ[c.O] Qbar l, S.π P ≤ RingHom.ker y ∧ Gd y ∧ y b ≠ 0) →
          ∃ ξ : S.A →ₐ[c.O] Qbar l, VPt S ξ ∧ S.u.TI (RingHom.ker ξ) ∧ P ≤ RingHom.ker ξ ∧ Gd (ξ.comp S.inc) := by
  intro l _ c _ F C₀ n hF hn S P Gd hP hTI hext
  obtain ⟨-, -, hgr0, -, hFT, -, hr⟩ := Fr.gr_A hF hn S
  haveI := hFT
  haveI hPp : P.IsPrime := hP.1.1
  have hTI' : (¬ S.u.triP ≤ P ∧ ¬ S.u.triM ≤ P) ∧ (n = 3 → ¬ S.u.ee ≤ P) := hTI
  obtain ⟨x1, ⟨g1, i1, j1, hlt1, rfl⟩, hx1⟩ :=
    gen_out (s := {x | ∃ g i, ∃ j < i, x = S.u.r g i j}) hTI'.1.1
  obtain ⟨x2, ⟨g2, i2, j2, hlt2, rfl⟩, hx2⟩ :=
    gen_out (s := {x | ∃ g i j, i < j ∧ x = S.u.r g i j}) hTI'.1.2
  obtain ⟨x3, ⟨k3, hx3k⟩, hx3P, hx3ee⟩ :
      ∃ x3 : S.A, (∃ k, x3 ∈ S.gr k) ∧ x3 ∉ P ∧ (n = 3 → x3 ∈ S.u.ee) := by
    by_cases h3 : n = 3
    · obtain ⟨x, ⟨g, i, j, hodd, rfl⟩, hx⟩ :=
        gen_out (s := {x | ∃ g i j, Odd (Fr.w n i - Fr.w n j) ∧ x = S.u.r g i j}) (hTI'.2 h3)
      exact ⟨_, ⟨_, hr g i j⟩, hx, fun _ => Ideal.subset_span ⟨g, i, j, hodd, rfl⟩⟩
    · refine ⟨1, ⟨0, ?_⟩, (Ideal.ne_top_iff_one P).mp hPp.ne_top, fun h => absurd h h3⟩
      rw [hgr0]
      exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have ha : S.u.r g1 i1 j1 * S.u.r g2 i2 j2 * x3 ∉ P := by
    intro h
    rcases hPp.mem_or_mem h with h | h
    · rcases hPp.mem_or_mem h with h | h
      · exact hx1 h
      · exact hx2 h
    · exact hx3P h
  obtain ⟨b, hbP, hb⟩ := chev_prime S.B S.A P _ ha
  obtain ⟨y, hyP, hGd, hyb⟩ := hext b hbP
  obtain ⟨ξ0, hξ0, hξ0a, hPξ0⟩ := hb (Qbar l) (y : S.B →+* Qbar l) (fun x hx => hyP hx) hyb
  have hξ0' : ∀ x : S.B, ξ0 (S.inc x) = y x := fun x =>
    congrArg (fun f : S.B →+* Qbar l => f x) hξ0
  let ξ1 : S.A →ₐ[c.O] Qbar l :=
    { ξ0 with
      commutes' := fun r => by
        show ξ0 (algebraMap c.O S.A r) = algebraMap c.O (Qbar l) r
        rw [← S.inc.commutes r, hξ0', y.commutes r] }
  have hcomp : ξ1.comp S.inc = y := by
    ext x
    exact hξ0' x
  rw [map_mul, map_mul, mul_ne_zero_iff, mul_ne_zero_iff] at hξ0a
  obtain ⟨⟨h1, h2⟩, h3⟩ := hξ0a
  have hoff : S.u.OffTri (RingHom.ker ξ1) :=
    ⟨fun h => h1 (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g1, i1, j1, hlt1, rfl⟩))),
      fun h => h2 (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g2, i2, j2, hlt2, rfl⟩)))⟩
  obtain ⟨ξ', hV, hc', hz⟩ := UpperTheory.V.J.scale l c F C₀ n hF hn S ξ1 hoff
  have hTIξ : S.u.TI (RingHom.ker ξ') :=
    ⟨⟨fun h => h1 ((hz _ _ (hr g1 i1 j1)).mp
        (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g1, i1, j1, hlt1, rfl⟩)))),
      fun h => h2 ((hz _ _ (hr g2 i2 j2)).mp
        (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g2, i2, j2, hlt2, rfl⟩))))⟩,
      fun hn3 h => h3 ((hz _ _ hx3k).mp (RingHom.mem_ker.mp (h (hx3ee hn3))))⟩
  refine ⟨ξ', hV, hTIξ, ?_, ?_⟩
  · intro x hx
    have hh := Fr.min_hom hF hn S P hP
    unfold Fr.Space.IsHom at hh
    rw [hh] at hx
    refine (Ideal.span_le.mpr ?_) hx
    rintro z ⟨hzP, k, hzk⟩
    exact RingHom.mem_ker.mpr ((hz k z hzk).mpr (RingHom.mem_ker.mp (hPξ0 hzP)))
  · rw [hc', hcomp]
    exact hGd
end

section

set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem cont_of_small {X M K : Type} [TopologicalSpace X] [AddCommGroup M] [NormedField K]
    (f : X → M) (φ : M →+ K) (W : ℕ → AddSubgroup M)
    (hφ : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ a ∈ W N, ‖φ a‖ ≤ ε)
    (hc : ∀ N x, ∀ᶠ y in nhds x, f y - f x ∈ W N) : Continuous fun g => φ (f g) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := hφ (ε / 2) (half_pos hε)
  refine (hc N x).mono fun y hy => ?_
  rw [dist_eq_norm, ← map_sub]
  exact (hN _ hy).trans_lt (half_lt_self hε)

private theorem bdd_of_small {R K : Type} [CommRing R] [NormedField K] (I : Ideal R) [Finite (R ⧸ I)]
    (φ : R →+ K) (h : ∀ a ∈ I, ‖φ a‖ ≤ 1) : ∃ C : ℝ, ∀ b, ‖φ b‖ ≤ C := by
  let s := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
  have hs : ∀ q, Ideal.Quotient.mk I (s q) = q := Function.surjInv_eq _
  obtain ⟨C, hC⟩ := Finite.exists_le fun q : R ⧸ I => ‖φ (s q)‖
  refine ⟨C + 1, fun b => ?_⟩
  have h1 : b - s (Ideal.Quotient.mk I b) ∈ I := Ideal.Quotient.eq.1 (hs _).symm
  have h2 : φ b = φ (s (Ideal.Quotient.mk I b)) + φ (b - s (Ideal.Quotient.mk I b)) := by
    rw [← map_add (f := _), add_sub_cancel]
  rw [h2]
  exact (norm_add_le _ _).trans (add_le_add (hC _) (h _ h1))

private theorem finite_quot (O R : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing R]
    [Algebra O R] [IsCO O R] (k : ℕ) : Finite (R ⧸ maximalIdeal R ^ k) := by
  haveI : Finite (ResidueField R) := Finite.of_surjective _ (resMap_bijective O R).2
  haveI : Finite (R ⧸ maximalIdeal R) := ‹Finite (ResidueField R)›
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k

private theorem small_smul {B A K : Type} [CommRing B] [CommRing A] [Algebra B A] [NormedField K] [IsUltrametricDist K]
    (I : Ideal B) (x : A →+* K) (D : A →+ K) (hx : ∀ a, ‖x a‖ ≤ 1)
    (hD : ∀ f g, D (f * g) = x f * D g + x g * D f)
    (hs : ∀ ε : ℝ, 0 < ε → ∃ k, ∀ b ∈ I ^ k, ‖D (algebraMap B A b)‖ ≤ ε ∧ ‖x (algebraMap B A b)‖ ≤ ε)
    (hb : ∃ C : ℝ, ∀ b, ‖D (algebraMap B A b)‖ ≤ C)
    (E : Submodule B A) (hE : E.FG) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ a ∈ I ^ N • E, ‖D a‖ ≤ ε ∧ ‖x a‖ ≤ ε := by
  have hsm : ∀ (b : B) (e : A), D (b • e) = x (algebraMap B A b) * D e + x e * D (algebraMap B A b) := by
    intro b e
    rw [Algebra.smul_def, hD]
  have hmul : ∀ (u v : K) (s t : ℝ), ‖u‖ ≤ s → ‖v‖ ≤ t → 0 ≤ s → ‖u * v‖ ≤ s * t := fun u v s t hu hv h0 => by
    rw [norm_mul]
    exact mul_le_mul hu hv (norm_nonneg _) h0
  obtain ⟨C₀, hC₀⟩ := hb
  obtain ⟨C, hC0, hCE⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ e ∈ E, ‖D e‖ ≤ C := by
    obtain ⟨T, rfl⟩ := hE
    obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, ∀ t ∈ T, ‖D t‖ ≤ C₁ := by
      obtain ⟨M, hM⟩ := (T.image fun t => ‖D t‖).exists_le
      exact ⟨M, fun t ht => hM _ (Finset.mem_image_of_mem _ ht)⟩
    refine ⟨max (max C₀ C₁) 0, le_max_right _ _, fun e he => ?_⟩
    have h0 : C₀ ≤ max (max C₀ C₁) 0 := (le_max_left _ _).trans (le_max_left _ _)
    have h1 : C₁ ≤ max (max C₀ C₁) 0 := (le_max_right _ _).trans (le_max_left _ _)
    have h2 : (0 : ℝ) ≤ max (max C₀ C₁) 0 := le_max_right _ _
    induction he using Submodule.span_induction with
    | mem t ht => exact (hC₁ t ht).trans h1
    | zero => simpa using h2
    | add a b _ _ ha hb =>
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    | smul b e _ he =>
      rw [hsm]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · simpa using hmul _ _ 1 _ (hx _) he zero_le_one
      · simpa using hmul _ _ 1 _ (hx _) ((hC₀ b).trans h0) zero_le_one
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < min ε (ε / (C + 1)) := lt_min hε (div_pos hε hC1)
  have hδ1 : min ε (ε / (C + 1)) ≤ ε := min_le_left _ _
  have hδ2 : min ε (ε / (C + 1)) * C ≤ ε := by
    have h1 : min ε (ε / (C + 1)) * C ≤ ε / (C + 1) * (C + 1) :=
      mul_le_mul (min_le_right _ _) (by linarith) hC0 (div_pos hε hC1).le
    rwa [div_mul_cancel₀ _ hC1.ne'] at h1
  obtain ⟨k, hk⟩ := hs _ hδ
  refine ⟨k, fun a ha => ?_⟩
  refine Submodule.smul_induction_on ha (fun b hbk e he => ⟨?_, ?_⟩) (fun a a' h h' => ⟨?_, ?_⟩)
  · rw [hsm]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact (hmul _ _ _ _ (hk b hbk).2 (hCE e he) hδ.le).trans hδ2
    · exact (by simpa using hmul _ _ 1 _ (hx e) (hk b hbk).1 zero_le_one : _ ≤ _).trans hδ1
  · rw [Algebra.smul_def, map_mul]
    exact (by simpa using hmul _ _ _ 1 (hk b hbk).2 (hx e) hδ.le : _ ≤ _).trans hδ1
  · rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.1 h'.1)
  · rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.2 h'.2)

private theorem entry_cont {X B A K : Type} [TopologicalSpace X] [CommRing B] [CommRing A] [Algebra B A] [NormedField K]
    [IsUltrametricDist K] (I : Ideal B) (x : A →+* K) (D : A →+ K) (hx : ∀ a, ‖x a‖ ≤ 1)
    (hD : ∀ f g, D (f * g) = x f * D g + x g * D f)
    (hs : ∀ ε : ℝ, 0 < ε → ∃ k, ∀ b ∈ I ^ k, ‖D (algebraMap B A b)‖ ≤ ε ∧ ‖x (algebraMap B A b)‖ ≤ ε)
    (hb : ∃ C : ℝ, ∀ b, ‖D (algebraMap B A b)‖ ≤ C) (e : X → A)
    (hE : (Submodule.span B (Set.range e)).FG)
    (hc : ∀ N : ℕ, IsLocallyConstant fun g => (I ^ N • Submodule.span B (Set.range e)).mkQ (e g)) :
    Continuous (fun g => x (e g)) ∧ Continuous fun g => D (e g) := by
  have hW : ∀ (N : ℕ) (p : X), ∀ᶠ q in nhds p,
      e q - e p ∈ (I ^ N • Submodule.span B (Set.range e)).toAddSubgroup := fun N p => by
    refine (((IsLocallyConstant.iff_eventually_eq _).1 (hc N)) p).mono fun q hq => ?_
    exact (Submodule.Quotient.eq _).1 hq
  have hsm := small_smul I x D hx hD hs hb _ hE
  refine ⟨cont_of_small e x.toAddMonoidHom _ (fun ε hε => ?_) hW, cont_of_small e D _ (fun ε hε => ?_) hW⟩
  · obtain ⟨N, hN⟩ := hsm ε hε
    exact ⟨N, fun a ha => (hN a ha).2⟩
  · obtain ⟨N, hN⟩ := hsm ε hε
    exact ⟨N, fun a ha => (hN a ha).1⟩

private theorem char_cont {X B K : Type} [TopologicalSpace X] [CommRing B] [NormedField K] (I : Ideal B) (φ : B →+ K)
    (hs : ∀ ε : ℝ, 0 < ε → ∃ k, ∀ b ∈ I ^ k, ‖φ b‖ ≤ ε) (χ : X → B) (hc : AdicCont I χ) :
    Continuous fun g => φ (χ g) := by
  refine cont_of_small χ φ (fun N => (I ^ N).toAddSubgroup) hs fun N p => ?_
  refine (((IsLocallyConstant.iff_eventually_eq _).1 (hc N)) p).mono fun q hq => ?_
  exact Ideal.Quotient.eq.1 hq

private theorem der_small (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] {R A : Type} [CommRing R] [CommRing A]
    [Algebra c.O R] [IsCO c.O R] [Algebra c.O A] [Algebra R A] [IsScalarTower c.O R A] (ξ : A →ₐ[c.O] Qbar l)
    (D : A →ₗ[c.O] Qbar l) (hD : ∀ f g, D (f * g) = ξ f * D g + ξ g * D f) (ε : ℝ) (hε : 0 < ε) :
    ∃ k, ∀ b ∈ maximalIdeal R ^ k, ‖D (algebraMap R A b)‖ ≤ ε ∧ ‖ξ (algebraMap R A b)‖ ≤ ε := by
  have hDy : (D ∘ₗ (IsScalarTower.toAlgHom c.O R A).toLinearMap) ∈ PtDer (ξ.comp (IsScalarTower.toAlgHom c.O R A)) (Qbar l) :=
    fun f g => by
      show D (algebraMap R A (f * g)) = ξ (algebraMap R A f) * D (algebraMap R A g) + ξ (algebraMap R A g) * D (algebraMap R A f)
      rw [map_mul]
      exact hD _ _
  exact derCont l c R _ _ hDy ε hε

private theorem der_bdd (O : Type) {R A K : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing R]
    [Algebra O R] [IsCO O R] [CommRing A] [Algebra R A] [NormedField K] [Module O K] [Module O A]
    (D : A →ₗ[O] K) (hs : ∃ k, ∀ b ∈ maximalIdeal R ^ k, ‖D (algebraMap R A b)‖ ≤ 1) :
    ∃ C : ℝ, ∀ b, ‖D (algebraMap R A b)‖ ≤ C := by
  obtain ⟨k, hk⟩ := hs
  haveI := finite_quot O R k
  exact bdd_of_small (maximalIdeal R ^ k) (D.toAddMonoidHom.comp (algebraMap R A).toAddMonoidHom) hk

private theorem entry_cont' {O X B A K : Type} [CommRing O] [TopologicalSpace X] [CommRing B] [CommRing A] [Algebra B A]
    [Algebra O A] [NormedField K] [Algebra O K] [IsUltrametricDist K] (I : Ideal B) (x : A →ₐ[O] K) (D : A →ₗ[O] K)
    (hx : ∀ a, ‖x a‖ ≤ 1) (hD : ∀ f g, D (f * g) = x f * D g + x g * D f)
    (hs : ∀ ε : ℝ, 0 < ε → ∃ k, ∀ b ∈ I ^ k, ‖D (algebraMap B A b)‖ ≤ ε ∧ ‖x (algebraMap B A b)‖ ≤ ε)
    (hb : ∃ C : ℝ, ∀ b, ‖D (algebraMap B A b)‖ ≤ C) (e : X → A)
    (hE : (Submodule.span B (Set.range e)).FG)
    (hc : ∀ N : ℕ, IsLocallyConstant fun g => (I ^ N • Submodule.span B (Set.range e)).mkQ (e g)) :
    Continuous (fun g => x (e g)) ∧ Continuous fun g => D (e g) :=
  entry_cont I (x : A →+* K) D.toAddMonoidHom hx hD hs hb e hE hc

private theorem char_cont' {O X B A K : Type} [CommRing O] [TopologicalSpace X] [CommRing B] [CommRing A] [Algebra B A]
    [Algebra O A] [NormedField K] [Algebra O K] (I : Ideal B) (x : A →ₐ[O] K) (D : A →ₗ[O] K)
    (hs : ∀ ε : ℝ, 0 < ε → ∃ k, ∀ b ∈ I ^ k, ‖D (algebraMap B A b)‖ ≤ ε ∧ ‖x (algebraMap B A b)‖ ≤ ε)
    (χ : X → B) (hc : AdicCont I χ) (ps : X → A) (he : ∀ g, algebraMap B A (χ g) = ps g) :
    (Continuous fun g => x (ps g)) ∧ Continuous fun g => D (ps g) := by
  have h : ps = fun g => algebraMap B A (χ g) := funext fun g => (he g).symm
  subst h
  exact ⟨char_cont I ((x : A →+* K).toAddMonoidHom.comp (algebraMap B A).toAddMonoidHom)
      (fun ε hε => (hs ε hε).imp fun _ h b hb => (h b hb).2) χ hc,
    char_cont I (D.toAddMonoidHom.comp (algebraMap B A).toAddMonoidHom)
      (fun ε hε => (hs ε hε).imp fun _ h b hb => (h b hb).1) χ hc⟩

set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.J.derRep :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, IntPt S ξ → ∀ D ∈ PtDer ξ (Qbar l),
          (∀ i j, Continuous fun g => ξ (S.u.r g i j)) ∧ (∀ i j, Continuous fun g => D (S.u.r g i j)) ∧
          ∀ v i, (Continuous fun g => ξ (S.u.ψ v i g : S.A)) ∧ Continuous fun g => D (S.u.ψ v i g : S.A) := by
  intro l _ c _ F C₀ n hF hn S ξ hξ D hD
  obtain ⟨hco, -⟩ := Fr.co_B hF hn S
  haveI := hco
  have cone := (Fr.cone_u hF hn S).1
  have hD' : ∀ f g, D (f * g) = ξ f * D g + ξ g * D f := hD
  have hs : ∀ ε : ℝ, 0 < ε → ∃ k, ∀ b ∈ maximalIdeal S.B ^ k,
      ‖D (algebraMap S.B S.A b)‖ ≤ ε ∧ ‖ξ (algebraMap S.B S.A b)‖ ≤ ε :=
    der_small l c ξ D hD'
  have hb : ∃ C : ℝ, ∀ b, ‖D (algebraMap S.B S.A b)‖ ≤ C :=
    der_bdd c.O D ((hs 1 one_pos).imp fun _ h b hb => (h b hb).1)
  have ent := fun i j => entry_cont' (maximalIdeal S.B) ξ D hξ.1 hD' hs hb
    (fun g => S.u.r g i j) (cone.fg i j) (cone.cont i j)
  obtain ⟨χ, hχ, hχe⟩ := cone.psi
  exact ⟨fun i j => (ent i j).1, fun i j => (ent i j).2, fun v i =>
    char_cont' (maximalIdeal S.B) ξ D hs (χ v i) (hχ v i).1 (fun g => (S.u.ψ v i g : S.A)) (hχe v i)⟩
end
