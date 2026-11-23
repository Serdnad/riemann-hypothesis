module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedDim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HighestWeightIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FibreTraces.ComplOfNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FibreTraces.FibTrdeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.DualNumber
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Cu

private theorem lifts_map {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} {c : PD Φ.ι Γ (ResidueField Λ)} {R R' : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {P : PD Φ.ι Γ R} (h : Φ.Lifts a c P) (f : R →ₐ[Λ] R') :
    Φ.Lifts a c (P.map (f : R →+* R')) := by
  refine ⟨?_, h.cont.map _ fun y hy => ?_, ?_⟩
  · have h1 := h.pair.map (f : R →+* R')
    rwa [← RingHom.comp_assoc, AlgHom.comp_algebraMap] at h1
  · show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hy
  · rw [PD.map_map, ← h.red]
    congr 1
    exact RingHom.ext fun x => res_map f x

private theorem lc_dual {Γ k : Type} [TopologicalSpace Γ] [Field k] {f : Γ → DualNumber k}
    (h : AdicCont (maximalIdeal (DualNumber k)) f) : IsLocallyConstant f := by
  have hm : ∀ x : DualNumber k, x ∈ maximalIdeal (DualNumber k) → x.fst = 0 := fun x hx => by
    rwa [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not] at hx
  have h2 : maximalIdeal (DualNumber k) ^ 2 = ⊥ := by
    rw [sq, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [Ideal.mem_bot]
    ext <;> simp [hm x hx, hm y hy]
  refine IsLocallyConstant.desc f _ (h 2) fun x y e => ?_
  rw [Ideal.Quotient.eq, h2, Ideal.mem_bot, sub_eq_zero] at e
  exact e

private theorem hom_of_der {O A k : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing k] [Algebra O k]
    (x : A →ₐ[O] k) (D : A →ₗ[O] k) (hD : D ∈ PtDer x k) :
    ∃ y : A →ₐ[O] DualNumber k, ∀ f, (y f).fst = x f ∧ (y f).snd = D f := by
  have hD' : ∀ f g, D (f * g) = x f • D g + x g • D f := hD
  have h1 : D 1 = 0 := by
    have := hD' 1 1
    simp only [mul_one, map_one, one_smul] at this
    exact left_eq_add.1 this
  refine ⟨{ toFun := fun f => (x f, D f)
            map_one' := TrivSqZeroExt.ext (map_one x) h1
            map_mul' := fun f g => TrivSqZeroExt.ext (map_mul x f g) ?_
            map_zero' := TrivSqZeroExt.ext (map_zero x) (map_zero D)
            map_add' := fun f g => TrivSqZeroExt.ext (map_add x f g) (map_add D f g)
            commutes' := fun t => TrivSqZeroExt.ext (x.commutes t) ?_ }, fun f => ⟨rfl, rfl⟩⟩
  · refine Eq.trans ?_ (DualNumber.snd_mul ((x f, D f) : DualNumber k) (x g, D g)).symm
    show D (f * g) = x f * D g + D f * x g
    rw [hD', smul_eq_mul, smul_eq_mul, mul_comm (D f)]
  · show D (algebraMap O A t) = 0
    rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]

theorem UpperTheory.V.Cu.redA_of : RedTanA → RedA := by
  intro htan
  unfold RedTanA at htan
  unfold RedA
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hstd d C hB c hc hA hent R _ _ _ P hP S hS hY
  set I := redIdeal S P.r with hI
  by_cases htop : I = ⊤
  · haveI : Subsingleton (R ⧸ I) := Ideal.Quotient.subsingleton_iff.2 htop
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 htop
  let p : R →ₐ[Λ] R ⧸ I := Ideal.Quotient.mkₐ Λ I
  have hp : Function.Surjective p := Ideal.Quotient.mkₐ_surjective Λ I
  haveI : IsCO Λ (R ⧸ I) := co_quot Λ R (R ⧸ I) p hp
  haveI : IsCO Λ (DualNumber (ResidueField Λ)) := (co_res Λ).2
  have hr : ∀ g i j, res Λ R (P.r g i j) = c.r g i j := fun g i j =>
    congrArg (fun Q : PD Φ.ι Γ (ResidueField Λ) => Q.r g i j) hP.1.red
  have hn : ∀ v i j, res Λ R (P.n v i j) = c.n v i j := fun v i j =>
    congrArg (fun Q : PD Φ.ι Γ (ResidueField Λ) => Q.n v i j) hP.1.red
  have hz : ∀ g i j, i ≠ j → wt i j ∉ S → p (P.r g i j) = 0 := fun g i j h1 h2 =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨g, i, j, h1, h2, rfl⟩)
  have hsupp : Supp S c.r := fun g i j h1 h2 => by rw [← hr, ← res_map p, hz g i j h1 h2, map_zero]
  refine redDim (Λ := Λ) (R ⧸ I) (d + 20 * C) ?_
  let L : PtDer (res Λ (R ⧸ I)) (ResidueField Λ) →ₗ[ResidueField Λ]
      (Γ → M4 (ResidueField Λ)) × (Φ.ι → M4 (ResidueField Λ)) :=
    { toFun := fun D => (fun g => (P.r g).map (fun x => D.1 (p x)) * c.r g⁻¹,
        fun v => (P.n v).map (fun x => D.1 (p x)) * adj (c.n v))
      map_add' := fun D D' => Prod.ext
        (_root_.funext fun g => add_mul ((P.r g).map fun x => D.1 (p x)) ((P.r g).map fun x => D'.1 (p x)) _)
        (_root_.funext fun v => add_mul ((P.n v).map fun x => D.1 (p x)) ((P.n v).map fun x => D'.1 (p x)) _)
      map_smul' := fun t D => Prod.ext
        (_root_.funext fun g => Matrix.smul_mul t ((P.r g).map fun x => D.1 (p x)) _)
        (_root_.funext fun v => Matrix.smul_mul t ((P.n v).map fun x => D.1 (p x)) _) }
  have hy : ∀ D : PtDer (res Λ (R ⧸ I)) (ResidueField Λ), ∃ y : (R ⧸ I) →ₐ[Λ] DualNumber (ResidueField Λ),
      ∀ f, (y f).fst = res Λ (R ⧸ I) f ∧ (y f).snd = D.1 f := fun D =>
    hom_of_der _ D.1 D.2
  have hmem : ∀ D, L D ∈ Submodule.span (ResidueField Λ) (Φ.Tan S c) := fun D => by
    obtain ⟨y, hy⟩ := hy D
    have hl := lifts_map hP.1 (y.comp p)
    have h := redDual Φ _ S c _ (fun _ => rfl) hl.pair (fun i j => lc_dual (hl.cont i j))
      (fun g i j => ((hy _).1.trans (res_map p _)).trans (hr g i j))
      (fun v i j => ((hy _).1.trans (res_map p _)).trans (hn v i j))
      (fun g i j h1 h2 => by
        show y (p (P.r g i j)) = 0
        rw [hz g i j h1 h2, map_zero])
    refine Submodule.subset_span ?_
    convert h using 1
    refine Prod.ext (_root_.funext fun g => ?_) (_root_.funext fun v => ?_)
    · exact congrArg (· * c.r g⁻¹) (Matrix.ext fun i j => (hy _).2.symm)
    · exact congrArg (· * adj (c.n v)) (Matrix.ext fun i j => (hy _).2.symm)
  have hinj : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro D hD
    obtain ⟨y, h1⟩ := hy D
    obtain ⟨y0, h0⟩ := hy 0
    have e1 : ∀ g i j, D.1 (p (P.r g i j)) = 0 := fun g i j => by
      have e : (P.r g).map (fun x => D.1 (p x)) * c.r g⁻¹ = 0 := congrFun (congrArg Prod.fst hD) g
      have e' := congrArg (· * c.r g) e
      simp only [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one, zero_mul] at e'
      exact congrFun (congrFun e' i) j
    have e2 : ∀ v i j, D.1 (p (P.n v i j)) = 0 := fun v i j => by
      have e : (P.n v).map (fun x => D.1 (p x)) * adj (c.n v) = 0 := congrFun (congrArg Prod.snd hD) v
      have e' := congrArg (· * c.n v) e
      have hu : adj (c.n v) * c.n v = 1 := (hc.pair.low v).1.trans (one_smul _ _)
      simp only [mul_assoc, hu, mul_one, zero_mul] at e'
      exact congrFun (congrFun e' i) j
    have key : ∀ x, D.1 x = 0 → y x = y0 x := fun x hx =>
      TrivSqZeroExt.ext ((h1 x).1.trans (h0 x).1.symm) (((h1 x).2.trans hx).trans (h0 x).2.symm)
    have e : y.comp p = y0.comp p := by
      refine (hP.2 _ _ (lifts_map hP.1 (y0.comp p))).unique ?_ rfl
      exact PD.ext (MonoidHom.ext fun g => Matrix.ext fun i j => key _ (e1 g i j))
        (_root_.funext fun v => Matrix.ext fun i j => key _ (e2 v i j))
    refine Subtype.ext (LinearMap.ext fun x => ?_)
    obtain ⟨x, rfl⟩ := hp x
    have e3 : y (p x) = y0 (p x) := AlgHom.congr_fun e x
    rw [← (h1 _).2, e3, (h0 _).2]
  have hle := LinearMap.rank_le_of_injective (L.codRestrict _ hmem) fun x x' e => hinj (congrArg Subtype.val e)
  have hmemS : ∀ w : ℤ × ℤ, w ≠ (0, 0) → Ent c.r w → w ∈ S := by
    rintro w hw ⟨g, i, j, hij, hne⟩
    by_contra hS'
    have hij' : i ≠ j := by
      rintro rfl
      apply hw
      rw [← hij]
      simp [wt]
    exact hne (hsupp g i j hij' (by rw [hij]; exact hS'))
  have hcond : -wPs ∈ S ∨ (-wBe ∈ S ∧ -wTh ∈ S ∧ S ≠ yY) := by
    rcases hent with h | ⟨h1, h2⟩
    · exact Or.inl (hmemS _ (by decide) h)
    · exact Or.inr ⟨hmemS _ (by decide) h1,
        hmemS _ (by decide) h2, hY⟩
  refine hle.trans ((htan Φ _ hstd.ok d C hB c hc hA S hS hcond hsupp).trans ?_)
  push_cast
  rfl
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Cu

private theorem UpperTheory.V.Cu.FiberPointBoundedGenerators.fib_low {K : Type} [Field K] (E : Subfield K) (n : M4 K) (h : IsLow n) (h10 : n 1 0 ∈ E)
    (h20 : n 2 0 ∈ E) (h30 : n 3 0 ∈ E) (h21 : n 2 1 ∈ E) (i j : Fin 4) : n i j ∈ E := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 := congrFun (congrFun h1 1) 0
  have e2 := congrFun (congrFun h1 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, h2, h3] at e1 e2
  have h32 : n 3 2 ∈ E := by
    have : n 3 2 = -n 1 0 := by linear_combination e1
    rw [this]; exact neg_mem h10
  have h31 : n 3 1 ∈ E := by
    have : n 3 1 = n 2 0 - n 2 1 * n 1 0 := by linear_combination -e2
    rw [this]; exact sub_mem h20 (mul_mem h21 h10)
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [h3 i j hij]; exact zero_mem _
  · rw [h2]; exact one_mem _
  · fin_cases i <;> fin_cases j <;> first | assumption | exact absurd hij (by decide)

private theorem UpperTheory.V.Cu.FiberPointBoundedGenerators.fib_gen {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} (X : Space Φ a) {K : Type} [Field K] (y : X.A →+* K)
    (hne : ∀ i j, i ≠ j → y (X.P.r Φ.g0 i i) ≠ y (X.P.r Φ.g0 j j)) (hTor : TorusY)
    (hS : Supp yY (mapRep y X.P.r)) (e1 : Ent (mapRep y X.P.r) wBe) (e2 : Ent (mapRep y X.P.r) (-wBe))
    (e3 : Ent (mapRep y X.P.r) wTh) (e4 : Ent (mapRep y X.P.r) (-wTh)) :
    ∃ T : Finset K, T.card ≤ 2 + 4 * Nat.card Φ.ι ∧ ∀ E : Subfield K, (∀ b, y (algebraMap X.B X.A b) ∈ E) → (∀ t ∈ T, t ∈ E) →
      (∀ (p : K[X]) (x : K), p.Monic → (∀ n, p.coeff n ∈ E) → p.IsRoot x → x ∈ E) → ∀ z, y z ∈ E := by
  classical
  haveI := Fintype.ofFinite Φ.ι
  have hp := X.pair.map y
  obtain ⟨s, t, hst⟩ := hTor (mapRep y X.P.r) Φ.g0 hp.nrm hne hS e1 e2 e3 e4
  let u : Φ.ι × Fin 4 → K := fun x => y (X.P.n x.1 (![1, 2, 3, 2] x.2) (![0, 0, 0, 1] x.2))
  refine ⟨{s, t} ∪ Finset.univ.image u, ?_, fun E hB hT hE z => ?_⟩
  · refine (Finset.card_union_le _ _).trans (add_le_add Finset.card_le_two (Finset.card_image_le.trans ?_))
    simp [mul_comm]
  · have hc : ∀ g n, (mapRep y X.P.r g).charpoly.coeff n ∈ E := fun g n => by
      have : (mapRep y X.P.r g).charpoly.coeff n = y (algebraMap X.B X.A ((X.cp g).coeff n)) := by
        show ((X.P.r g).map y).charpoly.coeff n = _
        rw [Matrix.charpoly_map, ← X.cp_map, coeff_map, coeff_map]
      rw [this]; exact hB _
    have hr := hst E (hT _ (by simp)) (hT _ (by simp))
      (fun g => by rw [Matrix.trace_eq_neg_charpoly_coeff]; exact neg_mem (hc _ _))
      (fun i => hE _ _ (Matrix.charpoly_monic _) (hc Φ.g0) (by
        have hd : mapRep y X.P.r Φ.g0 = Matrix.diagonal fun i => mapRep y X.P.r Φ.g0 i i := hp.nrm.diagonal_diag.symm
        rw [IsRoot, hd, Matrix.charpoly_diagonal, eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)))
    have hu : ∀ x, u x ∈ E := fun x => hT _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ x)))
    have hn := fun v => FiberPointBoundedGenerators.fib_low E _ (hp.low v) (hu (v, 0)) (hu (v, 1)) (hu (v, 2)) (hu (v, 3))
    have hz : z ∈ (⊤ : Subalgebra X.B X.A) := trivial
    rw [← X.gen] at hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact hr _ _ _
      · exact hn _ _ _
    | algebraMap b => exact hB b
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

theorem UpperTheory.V.Cu.fibY_of : TorusY → FibY := by
  intro hTor
  unfold FibY
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hΦ X c hc R _ _ _ f hf q hq r hr hS e1 e2 e3 e4
  subst hr
  haveI := X.noeth
  haveI := X.ft
  letI : Algebra X.A R := (f : X.A →+* R).toAlgebra
  haveI : IsScalarTower Λ X.A R := IsScalarTower.of_algebraMap_eq fun z => (f.commutes z).symm
  have hff : IsScalarTower.toAlgHom Λ X.A R = f := AlgHom.ext fun _ => rfl
  obtain ⟨hx, hR⟩ := fibCpl (Λ := Λ) (A := X.A) (R := R) (fun R' _ _ _ g hg => by
    rw [hff] at hg ⊢
    obtain ⟨h, hh, hu⟩ := hf.2 R' (X.P.map (g : X.A →+* R')) ⟨X.pair_map g, X.cont_map g, by
      rw [← hf.1.red]
      exact congrArg (fun φ : X.A →ₐ[Λ] ResidueField Λ => X.P.map (φ : X.A →+* ResidueField Λ)) hg⟩
    exact ⟨h, X.hom_ext _ _ hh, fun h' e => hu h' (by rw [← e]; rfl)⟩)
  have hxB : ((maximalIdeal R).comap (algebraMap X.A R)).comap (algebraMap X.B X.A) = maximalIdeal X.B := by
    ext b
    show (f.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b ∈ maximalIdeal R ↔ _
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
  haveI hη : (q.comap (algebraMap X.A R)).IsPrime := Ideal.comap_isPrime _ q
  obtain ⟨t, h1, h2⟩ := UpperTheory.V.CA.c3b Λ _ (UpperTheory.V.CA.IsCL.of_isCO Λ X.B) hxB (q.comap (algebraMap X.A R))
    (Ideal.comap_mono (le_maximalIdeal hq.ne_top))
  obtain ⟨T, hT, hE⟩ := FiberPointBoundedGenerators.fib_gen X _ (fun i j hij e => by
    have e1 : f (X.P.r Φ.g0 i i) - f (X.P.r Φ.g0 j j) ∈ q :=
      Ideal.Quotient.eq.1 (IsFractionRing.injective (R ⧸ q) (FractionRing (R ⧸ q)) e)
    have e2 := (res_eq_zero_iff Λ R _).2 (le_maximalIdeal hq.ne_top e1)
    have e3 : ∀ i, res Λ R (f (X.P.r Φ.g0 i i)) = (residue Λ).comp a (Φ.χ i Φ.g0) := fun i => by
      rw [← hc.res.diag, ← hf.1.red]; rfl
    rw [map_sub, e3, e3] at e2
    exact (hΦ.ok.dist i j hij).ne_zero e2) hTor hS e1 e2 e3 e4
  have h3 := fibTrdeg (D := X.B ⧸ (q.comap (algebraMap X.A R)).comap (algebraMap X.B X.A))
    ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.quotientMap q (algebraMap X.A R) le_rfl)) T
    (by rw [RingHom.coe_comp]; exact (IsFractionRing.injective (R ⧸ q) _).comp Ideal.quotientMap_injective) Ideal.quotientMap_injective
    (fun E hB hT' hcl z => by
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact hE E (fun b => hB (Ideal.Quotient.mk _ b)) hT' hcl z)
  rw [h1] at h3
  have h4 : t ≤ 2 + 4 * Nat.card Φ.ι := le_trans (by exact_mod_cast h3) hT
  refine ((UpperTheory.V.CA.c3c _ hR).2 _ q le_rfl).trans ?_
  rw [h2]
  exact add_le_add le_rfl (by exact_mod_cast h4)
end
