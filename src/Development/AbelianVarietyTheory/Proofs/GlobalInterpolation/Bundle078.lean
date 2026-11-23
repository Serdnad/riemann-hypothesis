module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange

open GlobalTheory.Proof.NormalFormAtPrime

theorem relIndex_ne_zero_of_cover {V : Type} [AddCommGroup V] (H K : AddSubgroup V) (S : Finset V)
    (h : ∀ k ∈ K, ∃ s ∈ S, k - s ∈ H) : H.relIndex K ≠ 0 := by
  rw [← QuotientAddGroup.ker_mk' H, AddSubgroup.relIndex_ker]
  have hf : ((K.map (QuotientAddGroup.mk' H) : AddSubgroup (V ⧸ H)) : Set (V ⧸ H)).Finite := by
    refine (S.finite_toSet.image (QuotientAddGroup.mk' H)).subset ?_
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨s, hs, e⟩ := h k hk
    exact ⟨s, hs, (QuotientAddGroup.eq_iff_sub_mem.2 e).symm⟩
  have : Finite (K.map (QuotientAddGroup.mk' H)) := hf
  exact Nat.card_pos.ne'

variable {E : Type} [Field E] [NumberField E]

def lat (P : HeightOneSpectrum (𝓞 E)) (ι : Type) (c : E) : AddSubgroup (ι → E) where
  carrier := {u | ∀ i, IntAt P (c * u i)}
  zero_mem' := fun i => by simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P
  add_mem' := fun {a b} ha hb i => by
    have := (ha i).add (hb i)
    rwa [← mul_add] at this
  neg_mem' := fun {a} ha i => by
    have := IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (ha i)
    simpa using this

theorem lat_le {P : HeightOneSpectrum (𝓞 E)} {ι : Type} {c c' : E} (k : ℕ) (h : c' = (qOf P : E) ^ k * c) :
    lat P ι c ≤ lat P ι c' := fun u hu i => by
  rw [h, mul_assoc]
  exact intAt_pow_mul k (hu i)

theorem exists_fin {P : HeightOneSpectrum (𝓞 E)} (h : ∀ x : E, ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * x))
    {κ : Type} [Fintype κ] (x : κ → E) : ∃ m : ℕ, ∀ m', m ≤ m' → ∀ k, IntAt P ((qOf P : E) ^ m' * x k) := by
  choose m hm using h
  refine ⟨Finset.univ.sup fun k => m (x k), fun m' hm' k => intAt_pow_mono (le_trans ?_ hm') (hm (x k))⟩
  exact Finset.le_sup (f := fun k => m (x k)) (Finset.mem_univ k)

theorem exists_bound {P : HeightOneSpectrum (𝓞 E)} (h : ∀ x : E, ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * x))
    {ι : Type} [Fintype ι] [DecidableEq ι] (T : (ι → E) →ₗ[E] (ι → E)) :
    ∃ m : ℕ, ∀ m', m ≤ m' → ∀ (c : E) (u : ι → E), u ∈ lat P ι c → T u ∈ lat P ι ((qOf P : E) ^ m' * c) := by
  obtain ⟨m, hm⟩ := exists_fin h (fun p : ι × ι => T (Pi.single p.1 1) p.2)
  refine ⟨m, fun m' hm' c u hu l => ?_⟩
  have e : T u = ∑ s, u s • T (Pi.single s 1) := by
    conv_lhs => rw [show u = ∑ s, u s • (Pi.single s (1 : E) : ι → E) from by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]]

    simp only [map_sum, map_smul]
  rw [e, Finset.sum_apply, Finset.mul_sum]
  refine intAt_sum _ _ fun s _ => ?_
  have := (hu s).mul (hm m' hm' (s, l))
  convert this using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem affine : (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y)) → (∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0)) → (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ, (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧ ∀ a : E, IntAt P ((qOf P : E) ^ A * a) → ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s))) → ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E), ∃ A₀ B₀ : ℕ, ∀ A B : ℕ, A₀ ≤ A → B₀ ≤ B → (boxSum P A B (fun t => f (T t + b)) ≠ 0 ↔ boxSum P A B f ≠ 0) := by
  classical
  intro h1 h2 h3 E _ _ K _ _ P hP ι _ _ f N hf T b
  have hq := qOf_ne_zero P
  have hs : ∀ x : E, ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * x) := fun x => by
    obtain ⟨m, hm⟩ := (h1 E P 1 1).1 (fun _ => x)
    exact ⟨m, hm m le_rfl 0⟩
  have sep : ∀ A B : ℕ, ∀ s ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E (qOf P) A B),
      ∀ s' ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E (qOf P) A B),
      s - s' ∈ lat P ι ((qOf P : E) ^ B)⁻¹ → s = s' := fun A B s hs s' hs' h => by
    funext i
    exact (h3 E P hP A B).1 _ (Fintype.mem_piFinset.1 hs i) _ (Fintype.mem_piFinset.1 hs' i) (h i)
  have cov : ∀ A B : ℕ, ∀ v ∈ lat P ι ((qOf P : E) ^ A),
      ∃ s ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E (qOf P) A B), v - s ∈ lat P ι ((qOf P : E) ^ B)⁻¹ :=
    fun A B v hv => by
      choose s hs hs' using fun i => (h3 E P hP A B).2 (v i) (hv i)
      exact ⟨s, Fintype.mem_piFinset.2 hs, hs'⟩
  have inv : ∀ v, ∀ u ∈ lat P ι ((qOf P : E) ^ N)⁻¹, f (v + u) = f v := fun v u hu => by
    have := hf.2 v (((qOf P : E) ^ N)⁻¹ • u) hu
    rwa [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hq), one_smul] at this
  obtain ⟨m1, hm1⟩ := exists_bound hs T.toLinearMap
  obtain ⟨m2, hm2⟩ := exists_bound hs T.symm.toLinearMap
  obtain ⟨m3, hm3⟩ := exists_fin hs b
  obtain ⟨m, a1, a2, a3⟩ : ∃ m, m1 ≤ m ∧ m2 ≤ m ∧ m3 ≤ m := ⟨m1 + m2 + m3, by omega, by omega, by omega⟩
  have hT := hm1 m a1
  have hT' := hm2 m a2
  have hb : b ∈ lat P ι ((qOf P : E) ^ m) := hm3 m a3
  simp only [LinearEquiv.coe_coe] at hT hT'
  refine ⟨N + 2 * m, N + 2 * m, fun A B hA hB => ?_⟩
  obtain ⟨A, rfl⟩ := Nat.exists_eq_add_of_le hA
  obtain ⟨B, rfl⟩ := Nat.exists_eq_add_of_le hB
  set A' := N + 2 * m + A with hA'
  set B' := N + 2 * m + B with hB'
  let L : AddSubgroup (ι → E) := lat P ι ((qOf P : E) ^ B')⁻¹
  let L' : AddSubgroup (ι → E) := L.comap T.symm.toLinearMap.toAddMonoidHom
  have mL' : ∀ u, u ∈ L' ↔ T.symm u ∈ L := fun u => Iff.rfl
  have hL'le : L' ≤ lat P ι ((qOf P : E) ^ m * ((qOf P : E) ^ B')⁻¹) := fun u hu => by
    have := hT _ _ ((mL' u).1 hu)
    rwa [LinearEquiv.apply_symm_apply] at this
  have hleL' : lat P ι ((qOf P : E) ^ (B' + m))⁻¹ ≤ L' := fun u hu => by
    have := hT' _ _ hu
    rw [mL']
    convert this using 2
    field_simp
    ring
  have hLN : L ≤ lat P ι ((qOf P : E) ^ N)⁻¹ := lat_le (2 * m + B) (by rw [hB']; field_simp; ring)
  have hL'N : L' ≤ lat P ι ((qOf P : E) ^ N)⁻¹ := hL'le.trans (lat_le (m + B) (by rw [hB']; field_simp; ring))
  have hN0 : lat P ι ((qOf P : E) ^ N)⁻¹ ≤ lat P ι ((qOf P : E) ^ 0) := lat_le N (by field_simp)
  have hinj : Function.Injective fun t => T t + b := fun s t h => T.injective (add_right_cancel h)
  have key := h2 (ι → E) K f L L' (Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) A' B')
    ((Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) A' B').image fun t => T t + b)
    (relIndex_ne_zero_of_cover _ _ _ fun k hk => by
      obtain ⟨s, hs, e⟩ := cov 0 (B' + m) k (hN0 (hLN hk))
      exact ⟨s, hs, hleL' e⟩)
    (relIndex_ne_zero_of_cover _ _ _ fun k hk => cov 0 B' k (hN0 (hL'N hk)))
    (fun v u hu => inv v u (hLN hu)) (fun v u hu => inv v u (hL'N hu)) (sep A' B')
    (fun v hv => cov A' B' v (lat_le (c := (qOf P : E) ^ N) (2 * m + A) (by rw [hA']; ring) (hf.1 v hv)))
    (fun s hs s' hs' h => by
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hs'
      rw [mL', add_sub_add_right_eq_sub, ← map_sub, LinearEquiv.symm_apply_apply] at h
      rw [sep A' B' t ht t' ht' h])
    (fun v hv => by
      have e1 : v - b ∈ lat P ι ((qOf P : E) ^ (N + m)) :=
        sub_mem (lat_le (c := (qOf P : E) ^ N) m (by ring) (hf.1 v hv)) (lat_le N (by ring) hb)
      obtain ⟨s, hs, e⟩ := cov A' B' _ (lat_le A (by rw [hA']; ring) (hT' _ _ e1))
      refine ⟨T s + b, Finset.mem_image_of_mem _ hs, ?_⟩
      rw [mL']
      convert e using 1
      rw [show v - (T s + b) = (v - b) - T s by abel, map_sub, LinearEquiv.symm_apply_apply])
  rw [Finset.sum_image hinj.injOn] at key
  have hqK : (qOf P : K) ≠ 0 := by
    have : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast this
  have hw : (((qOf P : K) ^ B')⁻¹) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hqK))
  unfold boxSum
  rw [mul_ne_zero_iff_left hw, mul_ne_zero_iff_left hw]
  exact key.symm

end GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open scoped ContDiff

namespace GlobalTheory.Glob.JetChainLin

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem prod_pow_eq {σ M : Type} [CommMonoid M] (F : σ → M) (e : σ →₀ ℕ) {n : ℕ} (f : Fin n → σ)
    (hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset σ)) :
    (e.prod fun k n => F k ^ n) = ∏ i, F (f i) := by
  classical
  have h1 : ((Finsupp.toMultiset e).map F).prod = e.prod fun k n => F k ^ n := by
    rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index]
    · intro _; simp
    · intro _ _ _; rw [pow_add]
  rw [← h1, hm, Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn]
  rfl

theorem monomial_eq_prod {σ : Type} (e : σ →₀ ℕ) {n : ℕ} (f : Fin n → σ)
    (hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset σ)) :
    (MvPolynomial.monomial e (1 : ℂ)) = ∏ i, MvPolynomial.X (f i) := by
  rw [MvPolynomial.monomial_eq, prod_pow_eq (fun k => (MvPolynomial.X k : MvPolynomial σ ℂ)) e f hm]
  simp

theorem derivAt0_eq (G : VCx ι a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) (e : DVar ι a b →₀ ℕ) {n : ℕ}
    (f : Fin n → DVar ι a b) (hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset (DVar ι a b))) :
    iteratedFDeriv ℂ n G 0 (fun i => coordX (f i)) = derivAt0 G e := by
  classical
  have hG' : ContDiff ℂ ∞ G := contDiff_infty.2 hG
  have hc : (Finsupp.toMultiset e).card = n := by rw [hm]; simp
  have p : ((List.ofFn f).map coordX).Perm ((Finsupp.toMultiset e).toList.map coordX) := by
    refine List.Perm.map _ ?_
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, hm]
  have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.cml_perm p n (iteratedFDeriv ℂ _ G 0)
    (fun v σ => ReciprocityTheory.L2DbarEstimates.Y.zd_iteratedFDeriv_comp_perm isOpen_univ hG'.contDiffOn _ 0 trivial σ v)
    (by simp) (by simp [hc])
  have h3 : ∀ (n n' : ℕ) (h : n = n') (v : Fin n → VCx ι a b) (w : Fin n' → VCx ι a b), (∀ i, v i = w (i.cast h)) →
      iteratedFDeriv ℂ n G 0 v = iteratedFDeriv ℂ n' G 0 w := by
    intro n n' h v w hvw
    subst h
    exact congrArg _ (funext hvw)
  unfold derivAt0
  refine Eq.trans (congrArg _ (funext fun i => ?_)) (h2.trans (h3 _ _ hc.symm _ _ fun i => ?_))
  · simp
  · simp

theorem jetC_eq (cD : ι → ℂ) (G : VCx ι a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) (e : DVar ι a b →₀ ℕ) {n : ℕ}
    (f : Fin n → DVar ι a b) (hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset (DVar ι a b))) :
    jetC cD G e = (∏ i, cD (f i).1) * iteratedFDeriv ℂ n G 0 (fun i => coordX (f i)) := by
  rw [derivAt0_eq G hG e f hm, jetC, prod_pow_eq (fun k : DVar ι a b => cD k.1) e f hm]

theorem constr_prod_X (cD : ι → ℂ) (G : VCx ι a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) {n : ℕ}
    (f : Fin n → DVar ι a b) :
    (MvPolynomial.basisMonomials (DVar ι a b) ℂ).constr ℂ (jetC cD G) (∏ i, MvPolynomial.X (f i)) =
      (∏ i, cD (f i).1) * iteratedFDeriv ℂ n G 0 (fun i => coordX (f i)) := by
  classical
  have hm : Finsupp.toMultiset (Multiset.toFinsupp (↑(List.ofFn f) : Multiset (DVar ι a b))) =
      (↑(List.ofFn f) : Multiset (DVar ι a b)) := Multiset.toFinsupp_toMultiset _
  rw [← monomial_eq_prod _ f hm, ← jetC_eq cD G hG _ f hm]
  have := (MvPolynomial.basisMonomials (DVar ι a b) ℂ).constr_basis ℂ (jetC cD G)
    (Multiset.toFinsupp (↑(List.ofFn f) : Multiset (DVar ι a b)))
  rwa [MvPolynomial.coe_basisMonomials] at this

noncomputable def subst (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) :
    VCx ι a b →ₗ[ℂ] VCx ι a b where
  toFun z := fun τ i j => ∑ k : Fin b, ∑ l : Fin a, h τ i k * z τ k l * g τ l j
  map_add' z w := by
    funext τ i j
    simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c z := by
    funext τ i j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring

omit [Fintype ι] in
theorem subst_coordX (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) (k : DVar ι a b) :
    subst g h (coordX k) =
      ∑ p : Fin b × Fin a, (h k.1 p.1 k.2.1 * g k.1 k.2.2 p.2) • coordX (k.1, p.1, p.2) := by
  classical
  obtain ⟨t, k, l⟩ := k
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change ∑ k' : Fin b, ∑ l' : Fin a, h τ i k' * coordX (t, k, l) τ k' l' * g τ l' j = _
  by_cases hτ : τ = t
  · subst hτ
    rw [Finset.sum_eq_single (i, j), Finset.sum_eq_single k, Finset.sum_eq_single l]
    · simp [coordX]
    · intro l' _ hl; simp [coordX, hl]
    · simp
    · intro k' _ hk; simp [coordX, hk]
    · simp
    · rintro ⟨i', j'⟩ _ hne
      have : ¬ (i = i' ∧ j = j') := by
        rintro ⟨rfl, rfl⟩
        exact hne rfl
      simp [coordX, this]
    · simp
  · simp [coordX, hτ]

theorem jetC_comp_subst : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (cD : ι → ℂ) (G : VCx ι a b → ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ), (∀ k : ℕ, ContDiff ℂ k G) → ∀ m : DVar ι a b →₀ ℕ, jetC cD (fun z : VCx ι a b => G (fun τ i j => ∑ k : Fin b, ∑ l : Fin a, h τ i k * z τ k l * g τ l j)) m = (MvPolynomial.basisMonomials (DVar ι a b) ℂ).constr ℂ (jetC cD G) (MvPolynomial.aeval (fun k : DVar ι a b => ∑ i : Fin b, ∑ j : Fin a, (MvPolynomial.C (h k.1 i k.2.1 * g k.1 k.2.2 j) * MvPolynomial.X (k.1, i, j) : MvPolynomial (DVar ι a b) ℂ)) (MvPolynomial.monomial m (1 : ℂ))) := by
  intro ι _ a b cD G g h hG m
  classical
  let T : VCx ι a b →L[ℂ] VCx ι a b := LinearMap.toContinuousLinearMap (subst g h)
  have h1 : (fun z : VCx ι a b => G (fun τ i j => ∑ k : Fin b, ∑ l : Fin a, h τ i k * z τ k l * g τ l j)) =
      G ∘ T := rfl
  have hm : Finsupp.toMultiset m = (↑(List.ofFn (Finsupp.toMultiset m).toList.get) : Multiset (DVar ι a b)) := by
    rw [List.ofFn_get, Multiset.coe_toList]
  generalize (Finsupp.toMultiset m).toList.get = f at hm
  rw [h1, jetC_eq cD (G ∘ T) (fun k => (hG k).comp T.contDiff) m f hm, monomial_eq_prod m f hm,
    T.iteratedFDeriv_comp_right (hG _) 0 le_rfl, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    map_prod]
  have h2 : (fun i => T (coordX (f i))) = fun i =>
      ∑ p : Fin b × Fin a, (h (f i).1 p.1 (f i).2.1 * g (f i).1 (f i).2.2 p.2) • coordX ((f i).1, p.1, p.2) :=
    funext fun i => subst_coordX g h (f i)

  rw [h2, ContinuousMultilinearMap.map_sum, Finset.mul_sum]
  simp only [MvPolynomial.aeval_X, ← Fintype.sum_prod_type']

  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, ← MvPolynomial.smul_eq_C_mul, map_smul,
    constr_prod_X cD G hG (fun i => ((f i).1, (r i).1, (r i).2)), ContinuousMultilinearMap.map_smul_univ]
  simp only [smul_eq_mul]
  ring

end GlobalTheory.Glob.JetChainLin
end
