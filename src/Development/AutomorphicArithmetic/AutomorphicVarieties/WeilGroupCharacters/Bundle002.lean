module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Bundle001
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

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

private theorem a_mu (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (I : Subgroup G) (d : ℕ) (A : LocAb l G I d) (g : G) (hg : g ∈ muG l G) : A.a g = 1 := by
  have hc : (commutator G).topologicalClosure ≤ A.a.ker := by
    apply Subgroup.topologicalClosure_minimal
    · exact Abelianization.commutator_subset_ker A.a
    · exact (isClosed_singleton.preimage A.cont : IsClosed (A.a ⁻¹' {1}))
  obtain ⟨n, hn⟩ := CommGroup.mem_primaryComponent.mp hg
  have hpow : g ^ (l ^ n) ∈ (commutator G).topologicalClosure := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hn
    exact hn
  have h1 : A.a g ^ (l ^ n) = 1 := by
    rw [← map_pow]
    exact hc hpow
  have hx : (l ^ n) • Multiplicative.toAdd (A.a g) = 0 := by
    have := congrArg Multiplicative.toAdd h1
    simpa [toAdd_pow] using this
  have hl : l ^ n ≠ 0 := pow_ne_zero n (Fact.out : l.Prime).ne_zero
  rcases smul_eq_zero.mp hx with h | h
  · exact absurd h hl
  · have e : A.a g = Multiplicative.ofAdd (Multiplicative.toAdd (A.a g)) := rfl
    rw [e, h]
    rfl

private theorem factor (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (I : Subgroup G) (d : ℕ) (A : LocAb l G I d) (R : Type) [CommRing R] (m : Ideal R)
    [IsHausdorff m R] (hl : (l : R) ∈ m) (δ : G →* Rˣ) (hc : AdicCont m fun g => ((δ g : Rˣ) : R))
    (hr : ∀ g, ((δ g : Rˣ) : R) - 1 ∈ m) (hm : ∀ g ∈ muG l G, δ g = 1) :
    ∃ χ : Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l]) →* Rˣ, AdicCont m (fun x => ((χ x : Rˣ) : R)) ∧
      ∀ g, χ (A.a g) = δ g := by
  classical
  have key : ∀ x : R, x - 1 ∈ m → ∀ k : ℕ, x ^ (l ^ k) - 1 ∈ m ^ (k + 1) := by
    intro x hx k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have hy : x ^ (l ^ k) - 1 ∈ m := Ideal.pow_le_self (Nat.succ_ne_zero k) ih
      have h1 : Ideal.Quotient.mk m (x ^ (l ^ k)) = 1 := by
        rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk m), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        exact hy
      have hS : (∑ i ∈ Finset.range l, (x ^ (l ^ k)) ^ i) ∈ m := by

        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
        simp only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        rw [← map_natCast (Ideal.Quotient.mk m), Ideal.Quotient.eq_zero_iff_mem]
        exact hl
      have e : x ^ (l ^ (k + 1)) - 1 = (∑ i ∈ Finset.range l, (x ^ (l ^ k)) ^ i) * (x ^ (l ^ k) - 1) := by
        rw [geom_sum_mul, ← pow_mul, ← pow_succ]
      rw [e, pow_succ' m (k + 1)]
      exact Ideal.mul_mem_mul hS ih
  have hk : ∀ g, A.a g = 1 → ∀ N : ℕ, ((δ g : Rˣ) : R) - 1 ∈ m ^ N := by
    intro g hg N
    let ρ : G →* (R ⧸ m ^ N)ˣ := (Units.map (Ideal.Quotient.mk (m ^ N)).toMonoidHom).comp δ
    have hρ : ∀ g, ρ g = 1 ↔ ((δ g : Rˣ) : R) - 1 ∈ m ^ N := by
      intro g
      rw [Units.ext_iff]
      show Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R) = 1 ↔ _
      rw [← map_one (Ideal.Quotient.mk (m ^ N)), Ideal.Quotient.eq]
    have hko : IsOpen (ρ.ker : Set G) := by
      have e : (ρ.ker : Set G) = (fun g => Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R)) ⁻¹' {1} := by
        ext g
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
        exact Units.ext_iff
      rw [e]
      exact hc N {1}
    have hopen : IsOpen (ρ.rangeRestrict.ker : Set G) := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hko
    haveI : Finite ρ.range := by
      haveI := Subgroup.quotient_finite_of_isOpen ρ.ker hko
      exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ).toEquiv
    have hp : IsPGroup l ρ.range := by
      rintro ⟨_, g', rfl⟩
      refine ⟨N, ?_⟩
      apply Subtype.ext
      show ρ g' ^ l ^ N = 1
      rw [← map_pow, hρ, map_pow, Units.val_pow_eq_pow_val]
      exact Ideal.pow_le_pow_right (Nat.le_succ N) (key _ (hr g') N)
    have hmu : muG l G ≤ ρ.rangeRestrict.ker := by
      rw [MonoidHom.ker_rangeRestrict]
      intro g' hg'
      rw [MonoidHom.mem_ker]
      show Units.map (Ideal.Quotient.mk (m ^ N)).toMonoidHom (δ g') = 1
      rw [hm g' hg', map_one]
    have := A.univ ρ.range hp ρ.rangeRestrict hopen hmu (MonoidHom.mem_ker.mpr hg)
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hρ] at this
    exact this
  have hδ1 : ∀ g, A.a g = 1 → δ g = 1 := by
    intro g hg
    apply Units.ext
    have h0 := IsHausdorff.haus' (I := m) (((δ g : Rˣ) : R) - 1) (fun N => by
      rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
      exact hk g hg N)
    exact sub_eq_zero.mp h0
  let e := QuotientGroup.quotientKerEquivOfSurjective A.a A.surj
  let χ0 : G ⧸ A.a.ker →* Rˣ := QuotientGroup.lift A.a.ker δ
    (fun g hg => MonoidHom.mem_ker.mpr (hδ1 g (MonoidHom.mem_ker.mp hg)))
  let χ := χ0.comp e.symm.toMonoidHom
  have hχ : ∀ g, χ (A.a g) = δ g := by
    intro g
    have h' : e.symm (A.a g) = (g : G ⧸ A.a.ker) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    show χ0 (e.symm (A.a g)) = δ g
    rw [h']
    rfl
  refine ⟨χ, ?_, hχ⟩
  intro N s
  have hcl : IsClosed (A.a '' ((fun g => Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R)) ⁻¹' s)ᶜ) :=
    A.cont.isClosedMap _ (hc N s).isClosed_compl
  have heq : ((fun x => Ideal.Quotient.mk (m ^ N) ((χ x : Rˣ) : R)) ⁻¹' s)ᶜ =
      A.a '' ((fun g => Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R)) ⁻¹' s)ᶜ := by
    ext x
    constructor
    · intro hx
      obtain ⟨g, rfl⟩ := A.surj x
      exact ⟨g, by simpa [hχ] using hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      simpa [hχ] using hg
  rw [← heq] at hcl
  exact isClosed_compl_iff.mp hcl

theorem UpperTheory.V.W.lam_factor :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (n : ℕ) (r : Resid F O n) (d : F.Vl → ℕ) (A : ∀ v, LocAb l (F.Gv v) (F.Iv v) (d v)) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (v : F.Vl) (i : Fin n) (ψ₀ : F.Gv v →* Rˣ), r.IsPsi v i ψ₀ → ∀ ψ : F.Gv v →* Rˣ,
      r.IsPsi v i ψ ↔ ∃ χ : Multiplicative ((Fin (d v) → ℤ_[l]) × ℤ_[l]) →* Rˣ, AdicCont (maximalIdeal R) (fun x => ((χ x : Rˣ) : R)) ∧ (∀ x, res O R (χ x) = 1) ∧ ψ = ψ₀ * χ.comp (A v).a := by
  intro l _ F O _ _ _ _ _ _ _ n r d A R _ _ _ v i ψ₀ h0 ψ
  haveI hcomp : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hl : (l : R) ∈ maximalIdeal R := by
    rw [← res_eq_zero_iff O R, map_natCast, CharP.cast_eq_zero]
  constructor
  · intro hψ
    let δ : F.Gv v →* Rˣ := ψ * ψ₀⁻¹
    have hδc : AdicCont (maximalIdeal R) (fun g => ((δ g : Rˣ) : R)) := by
      intro N
      have hinv : ∀ u : Rˣ, Ring.inverse (Ideal.Quotient.mk (maximalIdeal R ^ N) (u : R)) =
          Ideal.Quotient.mk (maximalIdeal R ^ N) ((u⁻¹ : Rˣ) : R) := by
        intro u
        have e : Ideal.Quotient.mk (maximalIdeal R ^ N) (u : R) =
            ((Units.map (Ideal.Quotient.mk (maximalIdeal R ^ N)).toMonoidHom u : (R ⧸ maximalIdeal R ^ N)ˣ) :
              R ⧸ maximalIdeal R ^ N) := rfl
        rw [e, Ring.inverse_unit]
        rfl
      have h1 := hψ.cont N
      have h2 : IsLocallyConstant (fun g => Ring.inverse
          (Ideal.Quotient.mk (maximalIdeal R ^ N) ((ψ₀ g : Rˣ) : R))) :=
        (h0.cont N).comp (Ring.inverse : R ⧸ maximalIdeal R ^ N → R ⧸ maximalIdeal R ^ N)
      convert h1.mul h2 using 1
      funext g
      simp only [δ, MonoidHom.mul_apply, Units.val_mul, map_mul]
      rw [MonoidHom.inv_apply, (hinv (ψ₀ g)).symm]
      rfl
    have hδr : ∀ g, ((δ g : Rˣ) : R) - 1 ∈ maximalIdeal R := by
      intro g
      rw [← res_eq_zero_iff O R, map_sub, map_one]
      have e3 : res O R ((ψ₀ g : Rˣ) : R) * res O R (((ψ₀ g)⁻¹ : Rˣ) : R) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      simp only [δ, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_mul]
      rw [hψ.red g, ← h0.red g, e3, sub_self]
    have hδm : ∀ g ∈ muG l (F.Gv v), δ g = 1 := by
      intro g hg
      have e1 := hψ.mu ⟨g, hg⟩
      have e2 := h0.mu ⟨g, hg⟩
      have hh : ψ g = ψ₀ g := Units.ext (e1.trans e2.symm)
      simp only [δ, MonoidHom.mul_apply, MonoidHom.inv_apply, hh, mul_inv_cancel]
    obtain ⟨χ, hχc, hχ⟩ := factor l (F.Gv v) (F.Iv v) (d v) (A v) R (maximalIdeal R) hl δ hδc hδr hδm
    refine ⟨χ, hχc, ?_, ?_⟩
    · intro x
      obtain ⟨g, rfl⟩ := (A v).surj x
      rw [hχ g]
      have := hδr g
      rw [← res_eq_zero_iff O R, map_sub, map_one, sub_eq_zero] at this
      exact this
    · refine MonoidHom.ext fun g => ?_
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hχ g]
      simp only [δ, MonoidHom.mul_apply, MonoidHom.inv_apply]
      rw [mul_comm (ψ g), mul_inv_cancel_left]
  · rintro ⟨χ, hχc, hχr, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro N
      have h1 := h0.cont N
      have h2 : IsLocallyConstant (fun g => Ideal.Quotient.mk (maximalIdeal R ^ N)
          ((χ ((A v).a g) : Rˣ) : R)) := (hχc N).comp_continuous (A v).cont
      convert h1.mul h2 using 1
      funext g
      rfl
    · intro g
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, map_mul, hχr, mul_one]
      exact h0.red g
    · intro g
      have ha := a_mu l (F.Gv v) (F.Iv v) (d v) (A v) g g.2
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, ha, map_one, mul_one]
      exact h0.mu g
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.W.FramePullback

section Det

variable {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H]

private theorem chi_comap (D : GDet n A G) (φ : H →* G) (y : MonoidAlgebra A H) :
    (D.comap φ).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A φ y) := by
  change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp

private theorem lam_comap (D : GDet n A G) (φ : H →* G) (i : ℕ) (y : MonoidAlgebra A H) :
    (D.comap φ).lam i y = D.lam i (MonoidAlgebra.mapDomainRingHom A φ y) := by
  unfold GDet.lam
  rw [chi_comap]

private theorem tr_zero (D : GDet n A G) (hn : 1 ≤ n) : D.tr 0 = 0 := by
  have h1 : D.chi 0 = Polynomial.X ^ n := by
    have := D.homog (Polynomial A) Polynomial.X 1
    rw [map_one, mul_one] at this
    rw [← this, GDet.chi, map_zero, sub_zero]
    congr 1
    simp [MonoidAlgebra.one_def]
  unfold GDet.tr GDet.lam
  rw [h1, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

private theorem tr_dim_zero (D : GDet 0 A G) (y : MonoidAlgebra A G) : D.tr y = -1 := by
  have h1 : ∀ x, D.D (Polynomial A) x = D.D (Polynomial A) 0 := fun x => by
    have := D.homog (Polynomial A) 0 x
    rw [zero_smul, pow_zero, one_mul] at this
    exact this.symm
  have h2 : D.chi y = 1 := by rw [GDet.chi, h1, ← h1 1, map_one]
  unfold GDet.tr GDet.lam
  rw [h2]
  simp

private theorem ofRep_comap (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) :
    (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  refine GDet.ext fun B _ _ x => ?_
  change (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ x)).det = (GDet.repAlg (ρ.comp φ) B x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [GDet.repAlg]

end Det

private theorem adic_comp {Γ Γ' R : Type} [TopologicalSpace Γ] [TopologicalSpace Γ'] [CommRing R] {I : Ideal R}
    {f : Γ → R} (hf : AdicCont I f) {φ : Γ' → Γ} (hφ : Continuous φ) : AdicCont I fun x => f (φ x) :=
  fun m => (hf m).comp_continuous hφ

private theorem mu_map {l : ℕ} [Fact l.Prime] {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : G →* H) (hφ : Continuous φ) {g : G}
    (hg : g ∈ muG l G) : φ g ∈ muG l H := by
  obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.1 hg
  refine CommGroup.mem_primaryComponent.2 ⟨k, ?_⟩
  have h1 : g ^ l ^ k ∈ (commutator G).topologicalClosure := (QuotientGroup.eq_one_iff _).1 hk
  have h2 : (commutator G).topologicalClosure ≤ (commutator H).topologicalClosure.comap φ := by
    refine Subgroup.topologicalClosure_minimal _ ?_ ((Subgroup.isClosed_topologicalClosure _).preimage hφ)
    refine le_trans ?_ (Subgroup.comap_mono (Subgroup.le_topologicalClosure _))
    rw [← Subgroup.map_le_iff_le_comap, commutator, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have h3 : φ g ^ l ^ k ∈ (commutator H).topologicalClosure := by
    rw [← map_pow]; exact h2 h1
  exact (QuotientGroup.eq_one_iff _).2 h3

variable {l : ℕ} [Fact l.Prime] {F' F : GFrame l} (h : FHom F' F)

private theorem continuous_pullback_projection : Continuous h.π₀ := (h.π_cont.comp (continuous_subtype_val : Continuous (fun x : F'.G₀ => (x : F'.Γ)))).subtype_mk _

private theorem pullback_projection_frobenius (v) (g) : h.π₀ (F'.φ v g) = F.φ (h.vl v) (h.gv v g) := Subtype.ext (h.hφ v g).symm

private theorem pullback_projection_conj (g) : h.π₀ (F'.conj g) = F.conj (h.π₀ g) := by
  apply Subtype.ext
  change h.π (F'.c * g * F'.c⁻¹) = F.c * h.π g * F.c⁻¹
  rw [map_mul, map_mul, map_inv, h.hc]

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R]

private theorem pullback_projection_sign_eq (g) : F.eps O R (h.π₀ g) = F'.eps O R g := by
  change Units.map _ (F.ε (h.π g)) = Units.map _ (F'.ε g)
  rw [h.hε]

private theorem star_single (F : GFrame l) (n : ℕ) (g : F.G₀) :
    F.star O R n (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R) := by
  simp [GFrame.star, GFrame.starOp]

private theorem map_star0 (n : ℕ) (g : F'.G₀) :
    MonoidAlgebra.mapDomainRingHom R h.π₀ (F'.star O R n (MonoidAlgebra.single g 1)) =
      F.star O R n (MonoidAlgebra.single (h.π₀ g) 1) := by
  rw [star_single, star_single, pullback_projection_sign_eq, ← pullback_projection_conj, ← map_inv]
  simp

private theorem map_oEl {n : ℕ} (v : F'.Vl) (ψ : Fin n → F.Gv (h.vl v) →* Rˣ) (g : Fin n → F'.Gv v) :
    MonoidAlgebra.mapDomainRingHom R h.π₀ (F'.oEl v (fun i => (ψ i).comp (h.gv v)) g) =
      F.oEl (h.vl v) ψ fun i => h.gv v (g i) := by
  unfold GFrame.oEl
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  rw [Function.comp_apply, map_sub]
  simp [pullback_projection_frobenius]

end UpperTheory.V.W.FramePullback


open UpperTheory.V.W.FramePullback in
theorem UpperTheory.V.W.Pair.isEmpty_of_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R)
    (hn : n = 0) : IsEmpty F.St ∧ IsEmpty F.Vl := by
  subst hn
  refine ⟨⟨fun u => ?_⟩, ⟨fun v => ?_⟩⟩
  · have := p.I u 1 (one_mem _) 1
    rw [tr_dim_zero] at this
    exact one_ne_zero (neg_eq_zero.1 this)
  · have := p.Ord v (fun _ => 1) 1
    rw [tr_dim_zero] at this
    exact one_ne_zero (neg_eq_zero.1 this)

open UpperTheory.V.W.FramePullback in
theorem UpperTheory.V.W.exists_determinantPair_pullback :
    ∀ (l : ℕ) [Fact l.Prime] (F' F : GFrame l) (h : FHom F' F) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r' : Resid F' O n) (r : Resid F O n), h.Compat r' r → (n = 0 → IsEmpty F'.St) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R),
      ∃ p' : Pair r' R, p'.D = p.D.comap h.π₀ ∧ ∀ v i, p'.ψ v i = (p.ψ (h.vl v) i).comp (h.gv v) := by
  intro l _ F' F h O _ _ _ n r' r hc hn R _ _ _ p
  have hs : ∀ g : F'.G₀, MonoidAlgebra.mapDomainRingHom R h.π₀ (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (h.π₀ g) 1 := fun g => by simp
  refine ⟨⟨p.D.comap h.π₀, fun v i => (p.ψ (h.vl v) i).comp (h.gv v), fun i => ?_, ?_, fun v i => ⟨?_, fun g => ?_, fun g => ?_⟩,
    fun i g => ?_, fun v g k => ?_, fun u g hg k => ?_⟩, rfl, fun _ _ => rfl⟩
  · simp only [lam_comap, hs]
    exact adic_comp (p.cont i) (continuous_pullback_projection h)
  · have : (p.D.comap h.π₀).map (res O R : R →+* ResidueField O) =
        (p.D.map (res O R : R →+* ResidueField O)).comap h.π₀ := rfl
    rw [this, p.red, Resid.Dbar, ofRep_comap, Resid.Dbar]
    congr 1
    ext g : 1
    have e : r'.chib = fun i => (r.chib i).comp h.π₀ := funext hc.chib
    rw [e]; rfl
  · exact adic_comp (p.psi (h.vl v) i).cont (h.gv_cont v)
  · rw [hc.psib]
    exact (p.psi (h.vl v) i).red _
  · have hg : h.gv v g ∈ F.mu (h.vl v) := mu_map (h.gv v) (h.gv_cont v) g.2
    rw [hc.th v i g hg]
    exact (p.psi (h.vl v) i).mu ⟨_, hg⟩
  · rw [lam_comap, lam_comap, map_star0, hs, p.P]
  · rw [GDet.tr, lam_comap, map_mul, hs, map_oEl]
    exact p.Ord _ _ _
  · rw [GDet.tr, lam_comap, map_mul, map_sub, hs, hs, map_one]
    rcases hc.ip u g hg with h1 | ⟨u', hu'⟩
    · rw [h1, ← MonoidAlgebra.one_def, sub_self, mul_zero]
      exact tr_zero p.D (Nat.pos_of_ne_zero fun h0 => (hn h0).elim u)
    · exact p.I u' _ hu' _
end
