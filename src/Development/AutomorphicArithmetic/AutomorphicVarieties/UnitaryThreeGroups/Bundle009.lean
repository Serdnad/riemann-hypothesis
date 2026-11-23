module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsCoordOfNotMatIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

section SlopeTestRemainingChoices

variable {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] [IsNoetherianRing R]
  [NormedField K] [IsUltrametricDist K] [Algebra O K]

omit [IsNoetherianRing R] [IsUltrametricDist K] in
private theorem norm_mul_le_of_loc {f : R →ₐ[O] K} (hf : IsLocPt f) (x : R) {z : R} (hz : z ∈ maximalIdeal R) :
    ‖f (x * z)‖ ≤ ‖f z‖ := by
  rw [map_mul, norm_mul]
  by_cases h0 : f z = 0
  · simp [h0]
  have hp : 0 < ‖f z‖ := norm_pos_iff.2 h0
  have hx : ‖f x‖ ≤ 1 := by
    by_contra hx
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖f z‖⁻¹) (not_le.1 hx)
    have h1 := hf (x ^ n * z) (Ideal.mul_mem_left _ _ hz)
    rw [map_mul, map_pow, norm_mul, norm_pow] at h1
    have h2 := mul_lt_mul_of_pos_right hn hp
    rw [inv_mul_cancel₀ hp.ne'] at h2
    exact lt_asymm h1 h2
  exact mul_le_of_le_one_left hp.le hx

private theorem exists_rho {f : R →ₐ[O] K} (hf : IsLocPt f) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ z ∈ maximalIdeal R, ‖f z‖ ≤ ρ := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  have hsm : ∀ z ∈ s, z ∈ maximalIdeal R := fun z hz => hs ▸ Submodule.subset_span hz
  have hlt : (s.sup fun z => ‖f z‖₊) < 1 :=
    (Finset.sup_lt_iff (by norm_num)).2 fun z hz => hf z (hsm z hz)
  refine ⟨(s.sup fun z => ‖f z‖₊ : NNReal), NNReal.coe_nonneg _, hlt, fun z hz => ?_⟩
  have key : ∀ x : R, ‖f (x * z)‖ ≤ (s.sup fun z => ‖f z‖₊ : NNReal) := by
    rw [← hs] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      intro x
      exact (norm_mul_le_of_loc hf x (hsm z hz)).trans (Finset.le_sup (f := fun z => ‖f z‖₊) hz)
    | zero => intro x; simp
    | add a b _ _ ha hb =>
      intro x
      rw [mul_add, map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha x) (hb x))
    | smul a b _ hb =>
      intro x
      rw [smul_eq_mul, ← mul_assoc]
      exact hb _
  simpa using key 1

private theorem exists_pow {f : R →ₐ[O] K} (hf : IsLocPt f) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ maximalIdeal R ^ n, ‖f z‖ < ε := by
  obtain ⟨ρ, h0, h1, h⟩ := exists_rho hf
  have key : ∀ n : ℕ, ∀ z ∈ maximalIdeal R ^ (n + 1), ‖f z‖ ≤ ρ ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      intro z hz
      rw [pow_succ] at hz
      refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · rw [map_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih a ha) (h b hb) (norm_nonneg _) (pow_nonneg h0 _)
      · rw [map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
  exact ⟨n + 1, fun z hz => (key n z hz).trans_lt
    ((pow_le_pow_of_le_one h0 h1.le (Nat.le_succ n)).trans_lt hn)⟩

private theorem eq_of_dense {f f' : R →ₐ[O] K} (hf : IsLocPt f) (hf' : IsLocPt f') (s : K) (x : R)
    (T : Set R) (hT : ∀ y ∈ T, f' y = s * f y)
    (h : ∀ n : ℕ, ∃ y ∈ Submodule.span O T, x - y ∈ maximalIdeal R ^ n) : f' x = s * f x := by
  have hsp : ∀ y ∈ Submodule.span O T, f' y = s * f y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact hT z hz
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, mul_add]
    | smul a b _ hb => rw [map_smul, map_smul, hb, mul_smul_comm]
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hs : 0 < ‖s‖ + 1 := by positivity
  obtain ⟨n, hn⟩ := exists_pow hf (div_pos hε hs)
  obtain ⟨n', hn'⟩ := exists_pow hf' (div_pos hε hs)
  obtain ⟨y, hy, hxy⟩ := h (max n n')
  have e : f' x - s * f x = f' (x - y) - s * f (x - y) := by
    rw [map_sub, map_sub, hsp y hy]; ring
  have a1 := hn _ (Ideal.pow_le_pow_right (le_max_left _ _) hxy)
  have a2 := hn' _ (Ideal.pow_le_pow_right (le_max_right _ _) hxy)
  rw [e, zero_add]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  have a3 := mul_le_mul_of_nonneg_left a1.le (norm_nonneg s)
  have a4 : ε / (‖s‖ + 1) + ‖s‖ * (ε / (‖s‖ + 1)) = ε := by field_simp; ring
  linarith

end SlopeTestRemainingChoices

section Mon

variable {O R K Γ : Type} [CommRing O] [CommRing R] [Algebra O R] [Field K] [Algebra O K] [Group Γ]

private theorem mon_zero (r : Γ →* GG (m := 3) (R := R)) (f : R →ₐ[O] K) (e : ℤ)
    (h : ∀ g a b, e * wt a b < 0 → f ((r g).mat a b) = 0) (j : ℤ) (hj : e * j < 0) :
    ∀ y ∈ entMon r j, f y = 0 := by
  rintro y ⟨L, rfl, rfl⟩
  induction L with
  | nil => simp at hj
  | cons s L ih =>
    rw [List.map_cons, List.sum_cons, mul_add] at hj
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases hs : e * wt s.2.1 s.2.2 < 0
    · rw [h _ _ _ hs, zero_mul]
    · rw [ih (by omega), mul_zero]

private theorem mon_tor (r : Γ →* GG (m := 3) (R := R)) (f f' : R →ₐ[O] K) (t : Kˣ)
    (h : ∀ g a b, f' ((r g).mat a b) = ((t ^ wt a b : Kˣ) : K) * f ((r g).mat a b)) (j : ℤ) :
    ∀ y ∈ entMon r j, f' y = ((t ^ j : Kˣ) : K) * f y := by
  rintro y ⟨L, rfl, rfl⟩
  induction L with
  | nil => simp
  | cons s L ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.prod_cons, map_mul, map_mul, h, ih, _root_.zpow_add,
      Units.val_mul]
    ring

private theorem mat_ker (η : Γ →* ℤˣ) (r : Γ →* GG (m := 3) (R := R)) (c : Γ) (hc : η c = -1) (h1 : (r c).mat = 1) (g : Γ) :
    ∃ g' ∈ η.ker, (r g).mat = (r g').mat := by
  rcases Int.units_eq_one_or (η g) with h | h
  · exact ⟨g, h, rfl⟩
  · refine ⟨g * c⁻¹, by simp [MonoidHom.mem_ker, h, hc], ?_⟩
    have hl : (r c).left = 1 := Units.ext h1
    have e : g = g * c⁻¹ * c := by simp
    conv_lhs => rw [e]
    rw [map_mul r _ c, GG.mat, GG.mat, SemidirectProduct.mul_left, hl, map_one, mul_one]

end Mon

theorem UpperTheory.V.U3.model_signs :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (M : Model S (PadicAlgCl l)), l ≠ 2 → Marks η Ψ cc g₁ →
      ∀ f : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f →
        (NegZero M.𝒜 (f.comp M.q) ↔ Upper η (push f S.r.hom)) ∧ (PosZero M.𝒜 (f.comp M.q) ↔ Lower η (push f S.r.hom)) ∧
        ∀ f' : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f' → ∀ t : (PadicAlgCl l)ˣ,
          push f' S.r.hom = conjBy (tor _ t) (push f S.r.hom) → f'.comp M.q = act M.𝒜 (tz t) (f.comp M.q) := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S M _ hM f hf
  have h1 : (S.r.hom cc).mat = 1 := ((S.rep S.R).1 (AlgHom.id _ _)).1.atc
  have key : ∀ e : ℤ, (∀ j, e * j < 0 → ∀ x ∈ M.𝒜 j, f (M.q x) = 0) ↔
      ∀ g ∈ η.ker, ∀ a b, e * wt a b < 0 → f ((S.r.hom g).mat a b) = 0 := by
    intro e
    constructor
    · intro h g _ a b hab
      obtain ⟨x, hx, hq⟩ := M.ent g a b
      rw [← hq]
      exact h _ hab x hx
    · intro h j hj x hx
      have h' : ∀ g a b, e * wt a b < 0 → f ((S.r.hom g).mat a b) = 0 := by
        intro g a b hab
        obtain ⟨g', hg', e'⟩ := mat_ker η S.r.hom cc hM.ηc h1 g
        rw [e']
        exact h g' hg' a b hab
      have := eq_of_dense hf hf 0 (M.q x) (entMon S.r.hom j)
        (fun y hy => by rw [mon_zero _ f e h' j hj y hy, zero_mul]) (M.dense j x hx)
      rwa [zero_mul] at this
  refine ⟨?_, ?_, fun f' hf' t ht => ?_⟩
  · have := key 1
    simp only [one_mul] at this
    exact this
  · have := key (-1)
    simp only [neg_mul, one_mul, neg_lt_zero] at this
    exact this
  · have h' : ∀ g a b, f' ((S.r.hom g).mat a b) =
        ((t ^ wt a b : (PadicAlgCl l)ˣ) : PadicAlgCl l) * f ((S.r.hom g).mat a b) := by
      intro g a b
      have := (conjBy_tor (push f S.r.hom) t).1 g a b
      rw [← ht] at this
      exact this
    refine AlgHom.ext fun x => ?_
    induction x using DirectSum.Decomposition.inductionOn M.𝒜 with
    | zero => rw [map_zero, map_zero]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | @homogeneous j x =>
      rw [act_of_mem M.𝒜 _ _ x.2]
      exact eq_of_dense hf hf' _ (M.q x) (entMon S.r.hom j) (mon_tor _ f f' t h' j) (M.dense j x x.2)
end

section

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

private theorem zmat_map {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (c g₁ : G)
    (r : G →* GG (m := 3) (R := R)) (i j : Fin 3) : zmat c g₁ ((GG.map f).comp r) i j = f (zmat c g₁ r i j) := by
  simp only [zmat, Matrix.sub_apply, MonoidHom.comp_apply, GG.map_mat, Matrix.map_apply, map_sub]

private theorem normalised_map {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) {c g₁ : G}
    {r : G →* GG (m := 3) (R := R)} (h : Normalised c g₁ r) : Normalised c g₁ ((GG.map f).comp r) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [MonoidHom.comp_apply, GG.map_mat, h.atc]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  · rw [zmat_map, h.z12, map_zero]
  · rw [zmat_map, h.z21, map_zero]

private theorem map_reducible_three_dim {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (η : G →* ℤˣ)
    (Ψ : G →* Rˣ) : (GG.map f).comp (r0 η Ψ) = r0 η ((Units.map f.toMonoidHom).comp Ψ) := by
  ext g : 1
  refine SemidirectProduct.ext ?_ ?_
  · ext i j
    simp [r0, GG.map, tor_val, Matrix.diagonal_apply]
    split_ifs
    · simp only [← map_zpow, ← map_pow, Units.coe_map]
      rfl
    · exact map_zero f
  · simp [r0, GG.map]

private theorem zeta_sub_mem {O Γ R : Type} [CommRing O] [IsLocalRing O] [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R) (c g₁ : Γ) :
    zeta c g₁ r.hom - algebraMap O R (zeta c g₁ (r0 η Ψ)) ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O R, map_sub, sub_eq_zero]
  have h1 : (res O R) (zeta c g₁ r.hom) =
      zeta c g₁ ((GG.map (res O R : R →+* ResidueField O)).comp r.hom) :=
    (zmat_map (res O R : R →+* ResidueField O) c g₁ r.hom 0 0).symm
  have h2 : (GG.map (res O R : R →+* ResidueField O)).comp r.hom = r0 η (barChar O Ψ) := by
    ext1 g
    exact r.red g
  have h3 : r0 η (barChar O Ψ) = (GG.map (residue O)).comp (r0 η Ψ) := by
    rw [map_reducible_three_dim]
    rfl
  rw [h1, h2, h3]
  show zmat c g₁ ((GG.map (residue O)).comp (r0 η Ψ)) 0 0 = _
  rw [zmat_map]
  simp [zeta]

private theorem norm_coe_coefO_le_one {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) :
    ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  haveI := c.fin
  have hint : IsIntegral ℤ_[l] (x : PadicAlgCl l) := by
    have hx : IsIntegral ℤ_[l] x := Algebra.IsIntegral.isIntegral x
    exact hx.map c.O.val
  obtain ⟨p, hmon, hp⟩ := hint
  by_contra hgt
  push_neg at hgt
  rw [hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at hp
  have hcoef : ∀ i ∈ Finset.range p.natDegree,
      ‖Polynomial.eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) (x : PadicAlgCl l)
        (Polynomial.C (p.coeff i) * Polynomial.X ^ i)‖ ≤ ‖(x : PadicAlgCl l)‖ ^ i := by
    intro i _
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]
    have hc : ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
      exact PadicInt.norm_le_one _
    calc _ ≤ 1 * ‖(x : PadicAlgCl l)‖ ^ i := by gcongr
      _ = _ := one_mul _
  have hlt : ‖∑ i ∈ Finset.range p.natDegree, Polynomial.eval₂ (algebraMap ℤ_[l] (PadicAlgCl l))
      (x : PadicAlgCl l) (Polynomial.C (p.coeff i) * Polynomial.X ^ i)‖ <
      ‖(x : PadicAlgCl l)‖ ^ p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with hn | hn
    · rw [hn]
      simp
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
        (Finset.nonempty_range_iff.mpr hn.ne') (fun i => Polynomial.eval₂
          (algebraMap ℤ_[l] (PadicAlgCl l)) (x : PadicAlgCl l) (Polynomial.C (p.coeff i) * Polynomial.X ^ i))
      exact lt_of_le_of_lt (hle.trans (hcoef i hi)) (pow_lt_pow_right₀ hgt (Finset.mem_range.mp hi))
  have heq := eq_neg_of_add_eq_zero_left hp
  have hn := congrArg norm heq
  rw [norm_neg, norm_pow] at hn
  linarith

theorem UpperTheory.V.U3.twoPt_shape :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ}
      (S : SRing (N := N) (hι := hι) (U := U) (I := I) (c := cc) (g₁ := g₁)), l ≠ 2 → Marks η Ψ cc g₁ →
      ∀ f : S.R →ₐ[c.O] PadicAlgCl l, TwoPt (η := η) S.r.hom f →
        (TypeI η (push f S.r.hom) ∨ TypeII η (push f S.r.hom)) ∧
        ∀ f' : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f' → MatIso η.ker (mats (push f S.r.hom)) (mats (push f' S.r.hom)) →
          ∃ t : (PadicAlgCl l)ˣ, push f' S.r.hom = conjBy (tor (R := PadicAlgCl l) t) (push f S.r.hom) := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S hl2 hmk f htwo
  have hid : (GLift.map (AlgHom.id c.O S.R) S.r).hom = S.r.hom := by
    ext g : 1
    refine SemidirectProduct.ext ?_ ?_
    · ext i j
      simp [GLift.map, GG.map]
    · simp [GLift.map, GG.map]
  have hN : Normalised cc g₁ S.r.hom := by
    have h := ((S.rep S.R).1 (AlgHom.id c.O S.R)).1
    rwa [hid] at h
  have hmult : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, HasMult η (push g S.r.hom) := by
    intro g x
    simpa [push, GG.map] using S.r.hasMult x
  have hnorm_g : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, Normalised cc g₁ (push g S.r.hom) :=
    fun g => normalised_map (g : S.R →+* PadicAlgCl l) hN
  have hzeta_g : ∀ g : S.R →ₐ[c.O] PadicAlgCl l,
      zeta cc g₁ (push g S.r.hom) = g (zeta cc g₁ S.r.hom) :=
    fun g => zmat_map (g : S.R →+* PadicAlgCl l) cc g₁ S.r.hom 0 0
  obtain ⟨_, hz0u⟩ := zeta_reducible_rep_eq_sub_inv_and_isUnit η Ψ cc g₁ hmk
  have hmem := zeta_sub_mem S.r cc g₁
  have ha : ‖algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ))‖ = 1 := by
    obtain ⟨u, hu⟩ := hz0u
    have h1 := norm_coe_coefO_le_one c (zeta cc g₁ (r0 η Ψ))
    have h2 := norm_coe_coefO_le_one c (↑u⁻¹ : c.O)
    have hprod : algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)) *
        algebraMap c.O (PadicAlgCl l) (↑u⁻¹ : c.O) = 1 := by
      rw [← map_mul, ← hu, Units.mul_inv, map_one]
    have hn := congrArg norm hprod
    rw [norm_mul, norm_one] at hn
    change ‖((zeta cc g₁ (r0 η Ψ) : c.O) : PadicAlgCl l)‖ * ‖((↑u⁻¹ : c.O) : PadicAlgCl l)‖ = 1 at hn
    change ‖((zeta cc g₁ (r0 η Ψ) : c.O) : PadicAlgCl l)‖ = 1
    have key := mul_le_mul_of_nonneg_left h2 (norm_nonneg ((zeta cc g₁ (r0 η Ψ) : c.O) : PadicAlgCl l))
    rw [mul_one] at key
    exact le_antisymm h1 (by linarith)
  have hdec : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt g →
      ‖zeta cc g₁ (push g S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ))‖ < 1 := by
    intro g hg
    rw [hzeta_g, ← AlgHom.commutes g, ← map_sub]
    exact hg _ hmem
  have hne0 : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt g → zeta cc g₁ (push g S.r.hom) ≠ 0 := by
    intro g hg h0
    have h := hdec g hg
    rw [h0, zero_sub, norm_neg, ha] at h
    exact lt_irrefl _ h
  have h2 : ‖(2 : PadicAlgCl l)‖ = 1 := by
    have h2e : (2 : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) ((2 : ℕ) : ℚ_[l]) := by
      rw [Nat.cast_ofNat, map_ofNat]
    rw [h2e, PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hl2
  have hnn : ∀ g g' : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt g → IsLocPt g' →
      zeta cc g₁ (push g' S.r.hom) ≠ -zeta cc g₁ (push g S.r.hom) := by
    intro g g' hg hg' heq
    have e1 := hdec g hg
    have e2 := hdec g' hg'
    have hsum : (2 : PadicAlgCl l) * algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)) =
        -((zeta cc g₁ (push g S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ))) +
          (zeta cc g₁ (push g' S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)))) := by
      rw [heq]
      ring
    have hle := IsUltrametricDist.norm_add_le_max
      (zeta cc g₁ (push g S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)))
      (zeta cc g₁ (push g' S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)))
    have hn := congrArg norm hsum
    rw [norm_neg, norm_mul, h2, ha, one_mul] at hn
    have hm := max_lt e1 e2
    linarith
  have hf := htwo.1
  have hcases := shape_cases η (push f S.r.hom) cc g₁ two_ne_zero (hmult f) hmk.ηc hmk.ηg
    (hnorm_g f) (hne0 f hf)
  have htype : TypeI η (push f S.r.hom) ∨ TypeII η (push f S.r.hom) := by
    rcases hcases with h | h | h | h
    · exact Or.inl h
    · exact absurd h htwo.2.1
    · exact absurd h htwo.2.2
    · exact Or.inr h
  refine ⟨htype, ?_⟩
  intro f' hf' hiso
  exact conjBy_tor_of_iso η (push f S.r.hom) (push f' S.r.hom) cc g₁ two_ne_zero (hmult f) (hmult f')
    hmk.ηc hmk.ηg (hnorm_g f) (hnorm_g f') (hne0 f hf) (hne0 f' hf') (hnn f f' hf hf') htype hiso
end
