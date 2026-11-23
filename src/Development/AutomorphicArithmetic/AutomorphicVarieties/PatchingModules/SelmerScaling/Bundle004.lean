module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle008
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
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem bnd_of {A Fr Γ Γ' : Type} [CommRing A] [CommRing Fr] [Algebra A Fr] [TopologicalSpace Γ]
    [TopologicalSpace Γ'] (t : A) (φ : Γ' → A) (hφ : AdicCont (Ideal.span {t}) φ) (p : Γ → Γ') (hp : Continuous p) :
    BndF t fun g => algebraMap A Fr (φ (p g)) :=
  ⟨0, fun g => φ (p g), fun N => (hφ N).comp_continuous hp, fun g => by simp⟩

theorem UpperTheory.V.Pa.bndRho :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), BndM x.t (fun g : G.G₀ => x.ρX x.Fr (h.p₀ g)) ∧ BndM x.t (fun g : G.G₀ => x.ρX x.Fr (h.p₀ g⁻¹)) ∧ ∀ j, BndM x.t (kapF h k j) := by
  intro l _ L G G0 h n x k
  have hp : Continuous (h.p₀ : G.G₀ → G0.G₀) := by
    apply Continuous.subtype_mk
    exact h.cont.comp continuous_subtype_val
  have hpi : Continuous (fun g : G.G₀ => h.p₀ g⁻¹) := hp.comp continuous_inv
  have hρ : ∀ i j, AdicCont (Ideal.span {x.t}) (fun g : G0.G₀ => (mat x.ρ) g i j) := by
    intro i j
    have := x.cont i j
    rwa [PowerSeries.maximalIdeal_eq_span_X] at this
  refine ⟨fun i j => bnd_of x.t _ (hρ i j) _ hp, fun i j => bnd_of x.t _ (hρ i j) _ hpi, ?_⟩
  intro j i i'
  have hk := ((k.mem j).2.1 i i')
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hk
  exact bnd_of x.t _ hk _ hp
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.aaCO :
    ∀ (O B A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing B] [Algebra O B] [IsCO O B] [CommRing A] [Algebra B A] [Module.Finite B A] (N : Submodule B A), Function.Injective (algebraMap B A) → _root_.IsCompl (1 : Submodule B A) N → (∀ a ∈ N, ∀ b ∈ N, ∃ c ∈ maximalIdeal B, a * b = algebraMap B A c) → ∀ [Algebra O A] [IsScalarTower O B A], ∃ _ : IsCO O A, (∀ a, a ∈ maximalIdeal A ↔ a ∈ (maximalIdeal B).map (algebraMap B A) ⊔ Ideal.span (N : Set A)) ∧ (ired N).map (algebraMap B A) ≤ maximalIdeal A ^ 2 := by
  intro O B A _ _ _ _ _ _ _ _ _ _ N hinj hc hN _ _
  have hdec : ∀ a : A, ∃ b : B, ∃ n ∈ N, a = algebraMap B A b + n := by
    intro a
    have ha : a ∈ (1 : Submodule B A) ⊔ N := by rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, n, hn, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp hu
    exact ⟨b, n, hn, rfl⟩
  let S : Set A := {a | ∃ b ∈ maximalIdeal B, ∃ n ∈ N, a = algebraMap B A b + n}
  have hSmul : ∀ x a, a ∈ S → x * a ∈ S := by
    rintro x a ⟨b, hb, n, hn, rfl⟩
    obtain ⟨b', n', hn', rfl⟩ := hdec x
    obtain ⟨c, hc', hcn⟩ := hN n' hn' n hn
    refine ⟨b' * b + c, Ideal.add_mem _ (Ideal.mul_mem_left _ _ hb) hc', b' • n + b • n',
      N.add_mem (N.smul_mem _ hn) (N.smul_mem _ hn'), ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, map_add (f := _), map_mul, ← hcn]
    ring
  have hSadd : ∀ a a', a ∈ S → a' ∈ S → a + a' ∈ S := by
    rintro a a' ⟨b, hb, n, hn, rfl⟩ ⟨b', hb', n', hn', rfl⟩
    exact ⟨b + b', Ideal.add_mem _ hb hb', n + n', N.add_mem hn hn', by rw [map_add (f := _)]; ring⟩
  have h1 : (1 : A) ∉ S := by
    rintro ⟨b, hb, n, hn, e⟩
    have hn1 : n ∈ (1 : Submodule B A) :=
      Submodule.mem_one.mpr ⟨1 - b, by rw [map_sub, map_one, e]; ring⟩
    have hn0 : n = 0 := by
      have hmem : n ∈ (1 : Submodule B A) ⊓ N := ⟨hn1, hn⟩
      rw [hc.inf_eq_bot] at hmem
      exact (Submodule.mem_bot B).mp hmem
    rw [hn0, add_zero, ← map_one (algebraMap B A)] at e
    have hb1 := hinj e
    rw [← hb1] at hb
    exact (IsLocalRing.mem_maximalIdeal _).mp hb isUnit_one
  have hnon : ∀ a : A, a ∈ S → ¬IsUnit a := by
    rintro a ha ⟨u, rfl⟩
    apply h1
    have := hSmul (↑u⁻¹) _ ha
    rwa [Units.inv_mul] at this
  have hunit : ∀ a : A, a ∉ S → IsUnit a := by
    intro a ha
    obtain ⟨b, n, hn, rfl⟩ := hdec a
    have hb : b ∉ maximalIdeal B := fun hb => ha ⟨b, hb, n, hn, rfl⟩
    obtain ⟨c, hcm, hcn⟩ := hN n hn n hn
    have hu : IsUnit (b * b - c) := by
      by_contra h
      apply hb
      have h' : b * b - c ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr h
      have hbb : b * b ∈ maximalIdeal B := by simpa using Ideal.add_mem _ h' hcm
      exact ((IsLocalRing.maximalIdeal.isMaximal B).isPrime.mem_or_mem hbb).elim id id
    have hprod : (algebraMap B A b + n) * (algebraMap B A b - n) = algebraMap B A (b * b - c) := by
      rw [map_sub, map_mul, ← hcn]
      ring
    exact isUnit_of_mul_isUnit_left (by rw [hprod]; exact hu.map _)
  haveI : Nontrivial A := hinj.nontrivial
  haveI hloc : IsLocalRing A := by
    apply IsLocalRing.of_nonunits_add
    intro a a' ha ha'
    have hS' : ∀ x : A, x ∈ nonunits A → x ∈ S := fun x hx => by
      by_contra h
      exact hx (hunit x h)
    exact hnon _ (hSadd _ _ (hS' _ ha) (hS' _ ha'))
  have hmemS : ∀ a : A, a ∈ maximalIdeal A ↔ a ∈ S := by
    intro a
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h => by by_contra h'; exact h (hunit a h'), hnon a⟩
  have hM : ∀ a : A, a ∈ S ↔ a ∈ (maximalIdeal B).map (algebraMap B A) ⊔ Ideal.span (N : Set A) := by
    intro a
    constructor
    · rintro ⟨b, hb, n, hn, rfl⟩
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hb))
        (Ideal.mem_sup_right (Ideal.subset_span hn))
    · intro ha
      refine (hmemS a).mp ?_
      have hle : (maximalIdeal B).map (algebraMap B A) ⊔ Ideal.span (N : Set A) ≤ maximalIdeal A := by
        refine sup_le (Ideal.map_le_iff_le_comap.mpr fun b hb => ?_) (Ideal.span_le.mpr fun n hn => ?_)
        · exact (hmemS _).mpr ⟨b, hb, 0, N.zero_mem, by simp⟩
        · exact (hmemS _).mpr ⟨0, zero_mem _, n, hn, by simp⟩
      exact hle ha
  haveI hco : IsCO O A := co_finite O B A (fun x => by
    obtain ⟨b, n, hn, rfl⟩ := hdec x
    obtain ⟨o, ho⟩ := IsCO.res_surj (O := O) b
    refine ⟨o, (hmemS _).mpr ⟨b - algebraMap O B o, ho, n, hn, ?_⟩⟩
    rw [IsScalarTower.algebraMap_apply O B A, map_sub]
    ring)
  refine ⟨hco, fun a => (hmemS a).trans (hM a), ?_⟩
  refine Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr ?_)
  rintro b ⟨x, hx, y, hy, e⟩
  show algebraMap B A b ∈ maximalIdeal A ^ 2
  rw [← e, pow_two]
  exact Ideal.mul_mem_mul ((hmemS x).mpr ⟨0, zero_mem _, x, hx, by simp⟩)
    ((hmemS y).mpr ⟨0, zero_mem _, y, hy, by simp⟩)
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem chi_rep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [Matrix.charpoly, Matrix.charmatrix]
  congr 1
  rw [map_sub, MonoidAlgebra.mapRingHom_single, map_one]
  ext i j : 2
  simp [GDet.repAlg, Matrix.one_apply, Matrix.diagonal_apply]

private theorem rep_single {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Algebra B A] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) (b : B) :
    GDet.repAlg ρ A (MonoidAlgebra.mapRingHom G (algebraMap B A) (MonoidAlgebra.single g b)) =
      algebraMap B A b • ρ g := by
  rw [MonoidAlgebra.mapRingHom_single]
  ext i j
  simp [GDet.repAlg]

theorem UpperTheory.V.Pa.vrRel :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), (∀ v (g : Fin S.n → S.L.Gv v), (List.ofFn fun i => S.U.vr (S.G.φ v (g i)) - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.u.ψ v i (g i)))).prod = 0) ∧ (∀ w, ∀ g ∈ S.G.frame.Iu w, S.U.vr g = 1) ∧ (∀ j, (List.ofFn fun i => S.U.vr (S.P.ph j) - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.P.U j i))).prod = 0) ∧ (∀ j i, (List.ofFn fun k => if k = i then 1 else S.U.vr (S.P.ph j) - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.P.U j k))).prod * (S.U.vr (S.P.ta j) - 1 - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.P.y j i))) = 0) ∧ ∀ i g, algebraMap S.B S.U.AA (S.u.D.lam i (MonoidAlgebra.single g 1)) = (-1) ^ i * (S.U.vr g).charpoly.coeff (S.n - i) := by
  intro l _ S
  let Φ : MonoidAlgebra S.B S.G.G₀ →+* Matrix (Fin S.n) (Fin S.n) S.U.AA :=
    (GDet.repAlg S.U.vr S.U.AA).toRingHom.comp (MonoidAlgebra.mapRingHom S.G.G₀ (algebraMap S.B S.U.AA))
  have h1 : ∀ g : S.G.G₀, Φ (MonoidAlgebra.single g 1) = S.U.vr g := fun g =>
    (rep_single S.U.vr g (1 : S.B)).trans (by rw [map_one, one_smul])
  have h2 : ∀ b : S.B, Φ (MonoidAlgebra.single 1 b) =
      algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA b) := fun b =>
    (rep_single S.U.vr 1 b).trans (by rw [map_one, Algebra.algebraMap_eq_smul_one (A := Matrix _ _ _)])
  have hk : ∀ z ∈ pairGens S.u ∪ qGens (O := S.O) (F := S.G.frame) S.P.ph S.P.ta S.P.U S.P.y, Φ z = 0 := by
    intro z hz
    refine S.U.kills z ?_
    change z ∈ S.u.D.chBar _
    simp only [GDet.chBar, closureIdeal, TwoSidedIdeal.mem_iInf]
    exact fun N H => TwoSidedIdeal.subset_span (Or.inl (Or.inl (Or.inr hz)))
  refine ⟨fun v g => ?_, fun w g hg => ?_, fun j => ?_, fun j i => ?_, fun i g => ?_⟩
  · rw [← hk (S.G.frame.oEl v (S.u.ψ v) g) (Or.inl (Or.inl ⟨v, g, Or.inl rfl⟩)), GFrame.oEl, map_list_prod,
      List.map_ofFn]
    congr 2
    funext i
    dsimp only [Function.comp_apply]
    rw [map_sub, h1, h2]
  · have := hk _ (Or.inl (Or.inr ⟨w, g, (S.P.Ip w).symm ▸ hg, Or.inl rfl⟩))
    rwa [map_sub, h1, map_one, sub_eq_zero] at this
  · rw [← hk _ (Or.inr (Or.inl ⟨j, Or.inl rfl⟩)), q1El, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    dsimp only [Function.comp_apply]
    rw [map_sub, h1, h2]
  · rw [← hk _ (Or.inr (Or.inr ⟨j, i, Or.inl rfl⟩)), q2El, map_mul, map_list_prod, List.map_ofFn, map_sub, map_sub,
      h1, h2, map_one]
    congr 3
    funext k
    dsimp only [Function.comp_apply]
    split_ifs
    · rw [map_one]
    · rw [map_sub, h1, h2]
  · rw [← ((UpperTheory.V.CA.d_gmap S.u.D).2.2.1 (algebraMap S.B S.U.AA) _).2 i, S.U.det, MonoidAlgebra.mapRingHom_single,
      map_one, GDet.lam, chi_rep]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.discImp :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ Q : Ideal S.Bh, Q.IsPrime → DiscSt (S.u.D.map (algebraMap S.B S.Bh)) Q → S.x.a = S.n ∨ ¬ ired S.U.N ≤ Q := by
  intro l _ S Q hQ hs
  rcases (UpperTheory.V.Pa.urep_stable S.U Q hQ).1 hs with ha | ⟨y, hy, z, hz, b, hb, e⟩
  · exact Or.inl ha
  · exact Or.inr fun hle => hb (hle (Ideal.subset_span ⟨y, hy, z, hz, e⟩))
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem lower_entries_zero_of_commuting_triangular {K ι : Type} [Field K] {n : ℕ} (T : ι → Matrix (Fin n) (Fin n) K)
    (Y : Matrix (Fin n) (Fin n) K) (hT : ∀ g i j, j < i → T g i j = 0)
    (hd : ∀ i j, i ≠ j → ∃ g, T g i i ≠ T g j j)
    (hc : ∀ g i j, j < i → (T g * Y) i j = (Y * T g) i j) :
    ∀ (m : ℕ) (i j : Fin n), (n - (i : ℕ)) + (j : ℕ) = m → j < i → Y i j = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i j hm hji
    obtain ⟨g, hg⟩ := hd i j (ne_of_gt hji)
    have h1 : (T g * Y) i j = T g i i * Y i j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [hT g i k h, zero_mul]
        · have hk' : (i : ℕ) < k := h
          have := k.2
          rw [ih ((n - (k : ℕ)) + (j : ℕ)) (by omega) k j rfl (hji.trans h), mul_zero]
      · simp
    have h2 : (Y * T g) i j = Y i j * T g j j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · have hk' : (k : ℕ) < j := h
          rw [ih ((n - (i : ℕ)) + (k : ℕ)) (by omega) i k rfl (h.trans hji), zero_mul]
        · rw [hT g k j h, mul_zero]
      · simp
    have h3 := hc g i j hji
    rw [h1, h2] at h3
    have h4 : (T g i i - T g j j) * Y i j = 0 := by linear_combination h3
    exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 hg)

private theorem upper_triangular_mul {K : Type} [Field K] {n : ℕ} (U T : Matrix (Fin n) (Fin n) K)
    (hU : ∀ i j, j < i → U i j = 0) (hT : ∀ i j, j < i → T i j = 0) :
    ∀ i j, j < i → (U * T) i j = 0 :=
  _root_.UpperTheory.Reformulated.B.Qe38.upper_triangular_mul U T hU hT

private theorem conjugate_commutator_identity {K : Type} [Field K] {n : ℕ} (w wi r r' Y : Matrix (Fin n) (Fin n) K)
    (h1 : w * wi = 1) (h2 : r' * r = 1) :
    (wi * (r * Y * r' - Y) * w) * (wi * r * w) =
      (wi * r * w) * (wi * Y * w) - (wi * Y * w) * (wi * r * w) := by
  have e1 : ∀ M : Matrix (Fin n) (Fin n) K, w * (wi * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have e2 : ∀ M : Matrix (Fin n) (Fin n) K, r' * (r * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, e1, e2]

theorem UpperTheory.V.Pa.localInvariants_eq_zero :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (v : L.Vl) (Y : Matrix (Fin n) (Fin n) x.Fr), (∀ g i j, j < i → (x.wiX x.Fr v * dY G0.frame (x.ρX x.Fr) Y (G0.φ v g) * x.wX x.Fr v) i j = 0) → ∀ i j, j < i → (x.wiX x.Fr v * Y * x.wX x.Fr v) i j = 0 := by
  intro l _ L G G0 h n x v Y H i j hij
  obtain ⟨h1, -, -, h4, h5, h6, -, -⟩ := UpperTheory.V.Pa.oddDiag l L G G0 h n x x.Fr v
  refine lower_entries_zero_of_commuting_triangular (fun g : L.Gv v => x.wiX x.Fr v * x.ρX x.Fr (G0.φ v g) * x.wX x.Fr v)
    (x.wiX x.Fr v * Y * x.wX x.Fr v) (fun g => (h4 g).1) ?_ ?_ _ i j rfl hij
  · intro a b hab
    by_contra hcon
    push Not at hcon
    refine (x.N1 v).1 a b hab (MonoidHom.ext fun g => Units.ext ?_)
    have := hcon g
    rw [(h4 g).2 a, (h4 g).2 b] at this
    exact IsFractionRing.injective x.A x.Fr this
  · intro g a b hab
    have hinv : x.ρX x.Fr (G0.φ v g)⁻¹ * x.ρX x.Fr (G0.φ v g) = 1 := by
      rw [← h5, inv_mul_cancel, h6]
    have e := conjugate_commutator_identity (x.wX x.Fr v) (x.wiX x.Fr v) _ _ Y h1 hinv
    have z := upper_triangular_mul _ _ (H g) (h4 g).1 a b hab
    unfold dY at z
    rw [e, Matrix.sub_apply] at z
    exact sub_eq_zero.1 z
end
