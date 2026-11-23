module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle445
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle313
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle483
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle012
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle272
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle466
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
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.Pi
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.torsion_fibreDim_quotient_pDivGroupLevel :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (k m : ℕ),
      1 ≤ k → ∀ (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] [Module.Finite O B]
        [Module.Projective O B] (j : B →ₐc[O] G.A (k + m)) (ρ : G.A (k + m) →ₗ[O] B),
        (∀ b, ρ (j b) = b) → torsionIdeal (R := O) (A := G.A (k + m)) p ≤ kerIdeal j →
        ∀ q : PrimeSpectrum O,
          fibreDim (B ⧸ torsionIdeal (R := O) (A := B) (p ^ m)) q = p ^ (m * G.height) := by
  intro p _ O _ G k m hk B _ _ _ _ _ j ρ hρ hj q
  obtain ⟨r, μ, hr, hker, hμ, hμq⟩ := G.exists_mulPow_fibreRank_eq p O k m
  let jₗ := (j : B →ₐ[O] G.A (k + m)).toLinearMap
  let rjₗ := ((r.comp j) : B →ₐ[O] G.A k).toLinearMap
  let μₗ := (μ : G.A k →ₐ[O] G.A (k + m)).toLinearMap
  let mul := mulBy (R := O) (A := B) (p ^ m)
  let mulₗ := (mul : B →ₐ[O] B).toLinearMap
  have hjq : fibreRank jₗ q = fibreDim B q :=
    (FibreRanks.fibre_ranks O B (G.A (k + m)) (G.A (k + m)) jₗ).1 ρ hρ q
  have hlevel := fibreDim_eq_ker_mul_range j q
  rw [show fibreRank (j : B →ₐ[O] G.A (k + m)).toLinearMap q = _ from hjq, G.fibreDim_eq]
    at hlevel
  have hres := fibreDim_eq_ker_mul_range (r.comp j) q
  rw [G.fibreDim_eq] at hres
  have hle : RingHom.ker r ≤ kerIdeal j := by
    rw [hker]
    exact (torsionIdeal_le_of_dvd (dvd_pow_self p (by omega : k ≠ 0))).trans hj
  let J := kerIdeal (r.comp j)
  let φ : G.A (k + m) →ₐ[O] G.A k ⧸ J := (Ideal.Quotient.mkₐ O J).comp r
  have hφ : Function.Surjective φ := (Ideal.Quotient.mkₐ_surjective O J).comp hr
  have hkerφ : RingHom.ker φ = kerIdeal j := by
    have hcomap : RingHom.ker φ = J.comap (r : G.A (k + m) →ₐ[O] G.A k) := by
      ext a
      simp [φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [hcomap, show J = Ideal.map (r : G.A (k + m) →ₐ[O] G.A k) (kerIdeal j) from
      kerIdeal_comp r j, Ideal.comap_map_of_surjective (r : G.A (k + m) →ₐ[O] G.A k) hr,
      sup_eq_left]
    exact hle
  let e : (G.A (k + m) ⧸ kerIdeal j) ≃ₗ[O] (G.A k ⧸ J) :=
    ((Ideal.quotientEquivAlgOfEq O hkerφ).symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective hφ)).toLinearEquiv
  rw [← fibreDim_congr e q] at hres
  have hmul := fibreDim_eq_ker_mul_range mul q
  have hlin : jₗ ∘ₗ mulₗ = μₗ ∘ₗ rjₗ := by
    ext b
    change j (mulBy (R := O) (A := B) (p ^ m) b) = μ (r (j b))
    rw [map_mulBy, hμ]
  have hrank : fibreRank mulₗ q = fibreRank rjₗ q := by
    rw [← (FibreRanks.fibre_ranks O B B (G.A (k + m)) mulₗ).2.1 jₗ q hjq, hlin,
      (FibreRanks.fibre_ranks O B (G.A k) (G.A (k + m)) rjₗ).2.1 μₗ q (hμq q)]
  change fibreDim B q = fibreDim (B ⧸ kerIdeal mul) q * fibreRank mulₗ q at hmul
  rw [hrank] at hmul
  change fibreDim (B ⧸ kerIdeal mul) q = _
  have hp : 0 < p ^ (k * G.height) := pow_pos (Fact.out : p.Prime).pos _
  have hpow : p ^ ((k + m) * G.height) = p ^ (m * G.height) * p ^ (k * G.height) := by
    rw [Nat.add_mul, pow_add, mul_comm]
  refine (Nat.eq_of_mul_eq_mul_right hp ?_).symm
  rw [← hpow, hlevel, hmul, hres]
  ring
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open Module

theorem exists_lattice_map_of_symplecticBasis {La : Type} [AddCommGroup La] {g : ℕ}
    (EF : LinearMap.BilinForm ℤ La) (hB : EF.IsAlt) (b : Basis (Fin g ⊕ Fin g) ℤ La)
    (d : Fin g → ℤ) (hb : IsSymplecticBasisOfType EF b d) (M : ℕ) (u t : Fin g → ℤ)
    (ht : ∀ i, u i * d i = 1 + (M : ℤ) * t i) :
    ∃ L : (Fin g ⊕ Fin g → ℤ) →+ La,
      (∀ a, (∃ y, L a = M • y) ↔ ∃ c, a = M • c) ∧ (∀ x, ∃ a y, x = L a + M • y) ∧
      ∀ a c, ∃ k : ℤ, EF (L a) (L c) = omegaStd a c + M * k := by
  classical
  let w : Fin g ⊕ Fin g → ℤ := Sum.elim u 1
  have hw : ∀ j, IsCoprime (w j) (M : ℤ) := by
    rintro (i | i)
    · exact ⟨d i, -t i, by simp only [w, Sum.elim_inl]; linear_combination ht i⟩
    · exact isCoprime_one_left
  let S : (Fin g ⊕ Fin g → ℤ) →ₗ[ℤ] (Fin g ⊕ Fin g → ℤ) :=
    { toFun := fun a j => w j * a j
      map_add' := fun a c => by funext j; simp [mul_add]
      map_smul' := fun r a => by funext j; simp; ring }
  let L : (Fin g ⊕ Fin g → ℤ) →+ La := (b.equivFun.symm.toLinearMap ∘ₗ S).toAddMonoidHom
  have hrepr : ∀ v j, b.repr (b.equivFun.symm v) j = v j := fun v j => by
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hL : ∀ a j, b.repr (L a) j = w j * a j := fun a j => hrepr (S a) j
  refine ⟨L, fun a => ⟨?_, ?_⟩, fun x => ?_, fun a c => ?_⟩
  · rintro ⟨y, hy⟩
    have hdiv : ∀ j, (M : ℤ) ∣ a j := by
      intro j
      have := hL a j
      rw [hy, map_nsmul] at this
      have h2 : (M : ℤ) ∣ w j * a j := ⟨b.repr y j, by rw [← this]; simp⟩
      exact (hw j).symm.dvd_of_dvd_mul_left h2
    choose c hc using hdiv
    exact ⟨c, funext fun j => by simp [hc j]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨L c, map_nsmul L M c⟩
  · refine ⟨Sum.elim (fun i => d i * b.repr x (Sum.inl i)) (fun i => b.repr x (Sum.inr i)),
      b.equivFun.symm (Sum.elim (fun i => -(t i * b.repr x (Sum.inl i))) 0), ?_⟩
    apply b.repr.injective
    ext j
    rw [map_add (f := _), Finsupp.add_apply, hL, map_nsmul, Finsupp.smul_apply]
    rcases j with i | i
    · simp only [w, Sum.elim_inl, hrepr, nsmul_eq_mul]
      linear_combination (-(b.repr x (Sum.inl i))) * ht i
    · simp [w, hrepr]
  · refine ⟨∑ i, t i * (a (Sum.inl i) * c (Sum.inr i) - a (Sum.inr i) * c (Sum.inl i)), ?_⟩
    rw [hb.apply_eq_sum hB, omegaStd, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hL, w, Sum.elim_inl, Sum.elim_inr, Pi.one_apply, one_mul]
    linear_combination (a (Sum.inl i) * c (Sum.inr i) - a (Sum.inr i) * c (Sum.inl i)) * ht i

theorem exists_lattice_map_mod_of_perfect : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La),
  (∀ x, EF x x = 0) → Function.Injective EF → ∀ (e M : ℕ), (∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f) → M.Coprime e →
  ∃ L : (Fin (Module.finrank ℤ La / 2) ⊕ Fin (Module.finrank ℤ La / 2) → ℤ) →+ La,
    (∀ a, (∃ y, L a = M • y) ↔ ∃ c, a = M • c) ∧ (∀ x, ∃ a y, x = L a + M • y) ∧
    ∀ a c, ∃ k : ℤ, EF (L a) (L c) = omegaStd a c + M * k := by
  intro La _ _ _ EF halt hinj e M hperf hcop
  have hB : EF.IsAlt := halt
  obtain ⟨g, b, d, hb, -, -⟩ := exists_isSymplecticBasisOfType_pos hB hinj
  have hg : Module.finrank ℤ La / 2 = g := by
    rw [IsSymplecticBasisOfType.finrank_eq b, Fintype.card_fin]; omega
  rw [hg]
  have hde : ∀ i, d i ∣ (e : ℤ) := by
    intro i
    obtain ⟨x, hx⟩ := hperf (b.coord (Sum.inr i))
    have h1 := hb.apply_right x i
    rw [hx] at h1
    simp only [LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
      nsmul_eq_mul, mul_one] at h1
    exact ⟨b.repr x (Sum.inl i), by rw [h1, mul_comm]⟩
  have hc : ∀ i, IsCoprime (M : ℤ) (d i) := fun i =>
    (Nat.isCoprime_iff_coprime.2 hcop).of_isCoprime_of_dvd_right (hde i)
  choose p u hpu using hc
  exact exists_lattice_map_of_symplecticBasis EF hB b d hb M u (fun i => -p i)
    (fun i => by linear_combination hpu i)

end GlobalTheory
end

section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SymplecticLevelLift

open Matrix Module

theorem omegaStd_single {h : ℕ} (i j : Fin h ⊕ Fin h) :
    omegaStd (Pi.single i 1) (Pi.single j 1) = (-Matrix.J (Fin h) ℤ) i j := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [omegaStd, Matrix.J, Pi.single_apply, Matrix.one_apply, eq_comm]

theorem gram_eq {h : ℕ} {M : Type} [AddCommGroup M] {Ef : LinearMap.BilinForm ℤ M}
    {b : Basis (Fin h ⊕ Fin h) ℤ M} (hb : IsSymplecticBasis Ef b) (hE : Ef.IsAlt)
    (v : Fin h ⊕ Fin h → M) :
    (Matrix.of fun i j => Ef (v i) (v j)) =
      (b.toMatrix v)ᵀ * (-Matrix.J (Fin h) ℤ) * b.toMatrix v := by
  ext i j
  rw [of_apply, hb.apply_eq_sum hE]
  simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Basis.toMatrix_apply, Matrix.one_apply,
    Finset.sum_sub_distrib]
  ring

theorem exists_symplectic_equiv_congr : ∀ (h k : ℕ) (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (Ef : LinearMap.BilinForm ℤ M) (l : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] M), 0 < k → Module.finrank ℤ M = 2 * h → (∀ x, Ef x x = 0) → Function.Bijective Ef → (∀ a b, (k : ℤ) ∣ Ef (l a) (l b) - omegaStd a b) → ∃ B : (Fin h ⊕ Fin h → ℤ) ≃ₗ[ℤ] M, (∀ a b, Ef (B a) (B b) = omegaStd a b) ∧ ∀ a, ∃ m : M, l a - B a = (k : ℤ) • m := by
  intro h k M _ _ _ Ef l _ hrk halt hbij hl
  have hE : Ef.IsAlt := halt
  obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank hE hbij hrk
  set v : Fin h ⊕ Fin h → M := fun j => l (Pi.single j 1) with hv
  have hmem : (b.toMatrix v).map (Int.castRingHom (ZMod k)) ∈
      Matrix.symplecticGroup (Fin h) (ZMod k) := by
    rw [SymplecticGroup.mem_iff']
    have h1 : (Matrix.of fun i j => Ef (v i) (v j)).map (Int.castRingHom (ZMod k)) =
        (-Matrix.J (Fin h) ℤ).map (Int.castRingHom (ZMod k)) := by
      ext i j
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).2 (hl (Pi.single i 1) (Pi.single j 1))
      rw [omegaStd_single, Int.cast_sub, sub_eq_zero] at this
      simpa [hv] using this
    rw [gram_eq hb hE, Matrix.map_mul, Matrix.map_mul, Matrix.map_neg _ (map_neg _), map_J,
      transpose_map] at h1
    simpa using h1
  obtain ⟨N, hN, hNT⟩ := symplectic_zmod_lift h k _ hmem
  have hw : b.toMatrix (fun j => ∑ i, N i j • b i) = N := by
    ext i j
    rw [Basis.toMatrix_apply, b.repr_sum_self]
  obtain ⟨c, hc, hcv⟩ := hb.exists_basis_of_toMatrix_mem hE (hw.symm ▸ hN)
  have hcong : ∀ j, ∃ m : M, v j - c j = (k : ℤ) • m := by
    intro j
    have hd : ∀ i, ∃ t : ℤ, b.toMatrix v i j - N i j = k * t := fun i => by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).1 ?_
      have := congrFun (congrFun hNT i) j
      simp only [Matrix.map_apply, eq_intCast] at this
      rw [Int.cast_sub, this, sub_self]
    choose t ht using hd
    refine ⟨∑ i, t i • b i, ?_⟩
    rw [← b.sum_toMatrix_smul_self v j, hcv, ← Finset.sum_sub_distrib, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← sub_smul, ht, mul_smul]
  choose m hm using hcong
  refine ⟨c.equivFun.symm, fun x y => ?_, fun a => ⟨∑ j, a j • m j, ?_⟩⟩
  · have hr : ∀ (z : Fin h ⊕ Fin h → ℤ) i, c.repr (c.equivFun.symm z) i = z i := fun z i => by
      rw [← c.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hc.apply_eq_sum hE]
    simp only [hr, omegaStd]
  · have hla : l a = ∑ j, a j • v j := by
      conv_lhs => rw [← Finset.univ_sum_single a]

      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hv, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hla, c.equivFun_symm_apply, ← Finset.sum_sub_distrib, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [← smul_sub, hm, smul_comm]

end GlobalTheory.SymplecticLevelLift
end

section

open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem bc_prodMapOf_bijective_iff (R T A : Type) [CommRing R] [CommRing T] [CommRing A] [Algebra R T]
    [Algebra R A] (q : ℕ) (hq : 0 < q) (act : Multiplicative (ZMod q) →* (A ≃ₐ[R] A)) :
    Function.Bijective (prodMapOf T (T ⊗[R] A) q (bcAct T act)) ↔
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id T T) (prodMapOf R A q act)) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  classical
  let e1 : (T ⊗[R] A) ⊗[T] (T ⊗[R] A) ≃ₐ[T] T ⊗[R] (A ⊗[R] A) :=
    (Algebra.TensorProduct.cancelBaseChange R T T (T ⊗[R] A) A).trans
      (Algebra.TensorProduct.assoc R R T T A A)
  let e2 : T ⊗[R] (Multiplicative (ZMod q) → A) ≃ₐ[T] (Multiplicative (ZMod q) → T ⊗[R] A) :=
    Algebra.TensorProduct.piRight R T T (fun _ : Multiplicative (ZMod q) => A)
  have key : ∀ x, prodMapOf T (T ⊗[R] A) q (bcAct T act) x =
      e2 (Algebra.TensorProduct.map (AlgHom.id T T) (prodMapOf R A q act) (e1 x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _), map_add (f := _), map_add (f := _)]
    | tmul u v =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add u u' hu hu' => rw [TensorProduct.add_tmul, map_add (f := _), hu, hu', map_add (f := _), map_add (f := _), map_add (f := _)]
      | tmul t a =>
        induction v using TensorProduct.induction_on with
        | zero => simp
        | add v v' hv hv' => rw [TensorProduct.tmul_add, map_add (f := _), hv, hv', map_add (f := _), map_add (f := _), map_add (f := _)]
        | tmul t' a' =>
          funext g
          simp [e1, e2, Algebra.TensorProduct.cancelBaseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul,
            Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.piRight_tmul, mul_comm]
  have hf : ⇑(prodMapOf T (T ⊗[R] A) q (bcAct T act)) =
      e2 ∘ (Algebra.TensorProduct.map (AlgHom.id T T) (prodMapOf R A q act)) ∘ e1 := funext key
  rw [hf]
  constructor
  · intro h
    have := (e2.symm.bijective.comp h).comp e1.symm.bijective
    convert this using 1
    funext y; simp
  · intro h
    exact e2.bijective.comp (h.comp e1.bijective)

theorem prodMapOf_finite (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (q : ℕ) (hq : 0 < q)
    (act : Multiplicative (ZMod q) →* (A ≃ₐ[R] A)) : (prodMapOf R A q act).toRingHom.Finite := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hc : ((prodMapOf R A q act).toRingHom.comp
      (Algebra.TensorProduct.includeLeft (S := R) (A := A) (B := A)).toRingHom) =
      algebraMap A (Multiplicative (ZMod q) → A) := by
    ext x g
    simp [prodMapOf]
  have : (algebraMap A (Multiplicative (ZMod q) → A)).Finite := by
    exact RingHom.finite_algebraMap.2 inferInstance
  exact RingHom.Finite.of_comp_finite (hc ▸ this)

theorem eventually_prodMapOf_bijective : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (actA : Multiplicative (ZMod q) →* (A ≃ₐ[F.obj j] A)),
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      GlobalTheory.LocAcyc.IsZModTorsor c.pt (c.pt ⊗[F.obj j] A) q (GlobalTheory.TorsorColim.bcAct c.pt actA)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj k) (F.obj k ⊗[F.obj j] A) q
        (GlobalTheory.TorsorColim.bcAct (F.obj k) actA)) := by
  intro J _ _ F c hc q hq j A _ _ _ actA hT
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : Algebra.FinitePresentation (F.obj j) (A ⊗[F.obj j] A) :=
    Algebra.FinitePresentation.trans (F.obj j) A (A ⊗[F.obj j] A)
  have hb : letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) (prodMapOf (F.obj j) A q actA)) := by
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
    exact (bc_prodMapOf_bijective_iff (F.obj j) c.pt A q hq actA).1 hT.2.2.2
  obtain ⟨k₀, f₀, hk⟩ := GlobalTheory.T.bijective_baseChange_descends_filteredColimit J F c hc j _ _ (prodMapOf (F.obj j) A q actA)
    (prodMapOf_finite _ _ q hq actA) hb
  refine ⟨k₀, f₀, fun k f => ?_⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
  exact (bc_prodMapOf_bijective_iff (F.obj j) (F.obj k) A q hq actA).2 (hk k f)

end GlobalTheory.TorsorColim
end

section

open IsLocalRing GlobalTheory.Henselisation

noncomputable section

namespace GlobalTheory.Henselisation

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem Hens.of_trans {i j : EtNbhd R} (h : i ≤ j) (y : i.B) :
    Hens.of j (EtNbhd.trans h y) = Hens.of i y :=
  Ring.DirectLimit.of_f h y

theorem Hens.exists_of (hdir : IsDirected (EtNbhd R) (· ≤ ·)) (z : Hens R) :
    ∃ (i : EtNbhd R) (y : i.B), Hens.of i y = z :=
  haveI : IsDirectedOrder (EtNbhd R) := hdir
  Ring.DirectLimit.exists_of (G := fun i : EtNbhd R => i.B)
    (f := fun _ _ h => ⇑(EtNbhd.trans h)) z

theorem Hens.exists_of_fin (hdir : IsDirected (EtNbhd R) (· ≤ ·)) :
    ∀ (l : ℕ) (x : Fin l → Hens R), ∃ (i : EtNbhd R) (y : Fin l → i.B), ∀ k, Hens.of i (y k) = x k := by
  intro l
  induction l with
  | zero => exact fun x => ⟨EtNbhd.base, fun k => k.elim0, fun k => k.elim0⟩
  | succ l ih =>
    intro x
    obtain ⟨i, y, hy⟩ := ih (fun k => x k.castSucc)
    obtain ⟨j, z, hz⟩ := Hens.exists_of hdir (x (Fin.last l))
    obtain ⟨m, him, hjm⟩ := directed_of (· ≤ ·) i j
    refine ⟨m, Fin.lastCases (EtNbhd.trans hjm z) (fun k => EtNbhd.trans him (y k)), ?_⟩
    intro k
    induction k using Fin.lastCases with
    | last => dsimp only; rw [Fin.lastCases_last, Hens.of_trans, hz]
    | cast k => dsimp only; rw [Fin.lastCases_castSucc, Hens.of_trans, hy]

theorem flat_hens_of_stages (hdir : IsDirected (EtNbhd R) (· ≤ ·))
    (hinj : ∀ i : EtNbhd R, Function.Injective (Hens.of i))
    (halg : ∀ (i : EtNbhd R) (r : R), Hens.of i (algebraMap R i.B r) = algebraMap R (Hens R) r)
    (hflat : ∀ i : EtNbhd R, Module.Flat R i.B) : Module.Flat R (Hens R) := by
  have hsmul : ∀ (i : EtNbhd R) (r : R) (y : i.B), Hens.of i (r • y) = r • Hens.of i y := by
    intro i r y
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, halg]
  refine Module.Flat.iff_forall_isTrivialRelation.mpr ?_
  intro l f x hfx
  obtain ⟨i, y, hy⟩ := Hens.exists_of_fin hdir l x
  have h0 : ∑ k, f k • y k = 0 := by
    apply hinj i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum]
    simp only [hsmul, hy]
    exact hfx
  obtain ⟨k, a, z, hya, haf⟩ := Module.Flat.iff_forall_isTrivialRelation.mp (hflat i) h0
  refine ⟨k, a, fun j => Hens.of i (z j), fun m => ?_, haf⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hy m, hya m, map_sum]
  simp only [hsmul]

theorem flat_hens : ∀ (R : Type) [CommRing R] [IsLocalRing R], Module.Flat R (Hens R) :=
  fun R _ _ => flat_hens_of_stages (GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R) (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd R) (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R) (GlobalTheory.T.flat_localRing_pointedEtaleNeighbourhood R)

end GlobalTheory.Henselisation
end
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

theorem _root_.GlobalTheory.T.exists_oscillatorAction_unitaryGroup_hermitian : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ (G : Type) [Group G] (m : G →* Matrix ι ι ℂ), (∀ g, (m g)ᴴ * H * m g = H) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => m g *ᵥ v) Ω ∧ (∀ g, m g = 1 → ∀ f, Sm ρ f → Ω g f = f) ∧ (∀ [TopologicalSpace G], Continuous m → ∀ f, Sm ρ f → Continuous fun g => Ω g f) ∧ ∀ (s : Matrix ι ι ℂ) (g : G), s * s = 1 → (H * s).PosDef → s * m g = m g * s → ∀ f, Sm ρ f → (∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (I • s *ᵥ z) = 0) → Ω g f = dP s (m g) • f := by
  first | exact @GlobalTheory.RealWeil.UnitaryOsc.exists_osc | exact GlobalTheory.RealWeil.UnitaryOsc.exists_osc | (intros; apply GlobalTheory.RealWeil.UnitaryOsc.exists_osc <;> assumption)
end

section

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

theorem _root_.GlobalTheory.T.flagColumnUnipotent_mem_periodUnipotent_integralGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : n ⊕ Fin c) (y : n ⊕ Fin c → k), (∀ r, y r ∈ 𝒪[k]) → (∀ r, ¬ ordL c r < ordL c t → y r = 0) → ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c), x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0) := by
  first | exact @GlobalTheory.DiagVol.colE_mem_symN_KO | exact GlobalTheory.DiagVol.colE_mem_symN_KO | (intros; apply GlobalTheory.DiagVol.colE_mem_symN_KO <;> assumption)
end

section

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

theorem _root_.GlobalTheory.T.flagRowUnipotent_mem_periodUnipotent_integralGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : n ⊕ Fin c) (y : n ⊕ Fin c → k), (∀ s, y s ∈ 𝒪[k]) → (∀ s, ¬ ordL c t < ordL c s → y s = 0) → ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c), x.val = 1 + Matrix.of (fun r s => if r = t then y s else 0) := by
  first | exact @GlobalTheory.DiagVol.rowElt_mem | exact GlobalTheory.DiagVol.rowElt_mem | (intros; apply GlobalTheory.DiagVol.rowElt_mem <;> assumption)
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_etaleStage_divisor_strictHenselisation_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (b c : O) (s : T), s ≠ 0 → b * c = algebraMap T O s →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (b₁ c₁ : Localization.AtPrime Q),
        b₁ * c₁ = algebraMap T (Localization.AtPrime Q) s ∧ j b₁ = b ∧ j c₁ = c := by
  first | (exact @GlobalTheory.KeyOriginCut.exists_stage_divisor) | (exact GlobalTheory.KeyOriginCut.exists_stage_divisor) | (intros; apply GlobalTheory.KeyOriginCut.exists_stage_divisor  <;> assumption)
end
