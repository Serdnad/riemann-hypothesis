module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.LocalToGlobal.HermitianForms.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle053
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.BranchBlock

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem isBlock_of_mulVec' {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) {A' : Matrix (Fin N) (Fin N) E}
    {A : Matrix (Fin n) (Fin n) E} {c : E} (h1 : ∀ x, iniH hN (A' *ᵥ x) = A *ᵥ iniH hN x)
    (h2 : ∀ x, (A' *ᵥ x) (Br.iL hN) = c * x (Br.iL hN)) : BranchFormula.IsBlock hN A' A c := by
  have hne : ∀ a : Fin n, Br.iC hN a ≠ Br.iL hN := fun a h => absurd (congrArg Fin.val h) a.2.ne
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have h := congrFun (h1 (Pi.single (Br.iC hN b) 1)) a
    have e : iniH hN (Pi.single (Br.iC hN b) (1 : E)) = Pi.single b 1 := funext fun i => by
      simp only [iniH, Pi.single_apply, (Br.iC_inj hN).eq_iff]
    rw [e, mulVec_single_one, mulVec_single_one] at h
    exact h
  · have h := congrFun (h1 (Pi.single (Br.iL hN) 1)) a
    have e : iniH hN (Pi.single (Br.iL hN) (1 : E)) = 0 := funext fun i => Pi.single_eq_of_ne (hne i) _
    rw [e, mulVec_single_one, mulVec_zero] at h
    exact h
  · have h := h2 (Pi.single (Br.iC hN a) 1)
    rw [mulVec_single_one, Pi.single_eq_of_ne (hne a).symm, mul_zero] at h
    exact h
  · have h := h2 (Pi.single (Br.iL hN) 1)
    rw [mulVec_single_one, Pi.single_eq_same, mul_one] at h
    exact h

theorem rhoVr_brAt_eq_brStd : ∀ {E K ι : Type} [Field E] [Field K] [CharZero K] [Fintype ι] (emb : ι → E →+* K) {N n : ℕ}
    (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n), (∀ τ, Br.Interlace hN (lam τ) (sg τ)) →
    (∀ τ, Br.SameShift (lam τ) (sg τ)) → ∀ (t : E) (B' : GL (Fin n) E) (B : GL (Fin N) E),
    (∀ x, iniH hN ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) = (B' : Matrix (Fin n) (Fin n) E) *ᵥ iniH hN x) →
    (∀ x, t * ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) (Br.iL hN) = x (Br.iL hN)) →
    ∀ G : Formalism.L2.DIV.VV K lam, rhoVr emb sg B'⁻¹ (Br.brAt hN lam sg (fun τ => emb τ t) G) =
      Br.brStd hN lam sg (rhoVr emb lam B⁻¹ G) := by
  intro E K ι _ _ _ _ emb N n hN lam sg hI hS t B' B h1 h2 G
  have ht : t ≠ 0 := by
    intro h0
    have h := h2 (Pi.single (Br.iL hN) 1)
    rw [h0, zero_mul, Pi.single_eq_same] at h
    exact zero_ne_one h
  have hBA : ∀ x, (B : Matrix (Fin N) (Fin N) E) *ᵥ (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x) = x := by
    intro x
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hAB : ∀ y, ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((B' : Matrix (Fin n) (Fin n) E) *ᵥ y) = y := by
    intro y
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hblk : BranchFormula.IsBlock hN ((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
      ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t := by
    refine isBlock_of_mulVec' hN (fun x => ?_) (fun x => ?_)
    · have h := h1 (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x)
      rw [hBA] at h
      rw [h, hAB]
    · have h := h2 (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x)
      rw [hBA] at h
      exact h.symm
  have e1 : ∀ {m : ℕ} (g : GL (Fin m) E) (τ : ι) (a b : Fin m),
      ((invTrK (embGL emb g) τ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) a b =
        emb τ (((g⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) b a) := fun g τ a b => rfl
  have key := BranchFormula.brAt_eq_pullback hN hI hS (invTrK (embGL emb B')) (invTrK (embGL emb B))
    (fun τ => emb τ t) (fun τ => (map_ne_zero _).2 ht) (fun τ => by
      refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> simp only [e1]
      · rw [hblk.1]
      · rw [(hblk.2.1 a).2, map_zero]
      · rw [(hblk.2.1 a).1, map_zero]
      · rw [hblk.2.2]) G
  show rhoK sg (invTrK (embGL emb B'⁻¹)) _ = Br.brStd hN lam sg (rhoK lam (invTrK (embGL emb B⁻¹)) G)
  rw [map_inv (embGL emb), map_inv (embGL emb), map_inv invTrK, map_inv invTrK]
  exact key.symm

end GlobalTheory.BranchBlock
end
end

section

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory.SplitUnram



theorem isUnramifiedAt_of_isSplitAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (w : HeightOneSpectrum (𝓞 L)), IsSplitAt w →
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  intro L _ _ _ w hw
  obtain ⟨u, hne, hu⟩ := hw
  set K := maximalRealSubfield L
  set p : Ideal (𝓞 K) := w.asIdeal.under (𝓞 K) with hpdef
  have hup : u.asIdeal.under (𝓞 K) = p := by
    have := congrArg HeightOneSpectrum.asIdeal hu
    exact this
  haveI : w.asIdeal.LiesOver p := ⟨rfl⟩
  haveI : u.asIdeal.LiesOver p := ⟨hup.symm⟩
  have hp0 : p ≠ ⊥ := (w.under (𝓞 K)).ne_bot
  haveI hpm : p.IsMaximal := (w.under (𝓞 K)).isMaximal
  have hwmem : w.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).2 ⟨w.isPrime, inferInstance⟩
  have humem : u.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).2 ⟨u.isPrime, inferInstance⟩
  have hneI : u.asIdeal ≠ w.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have hsum := Ideal.sum_ramification_inertia (𝓞 L) K L (p := p) hp0
  rw [Algebra.IsQuadraticExtension.finrank_eq_two K L] at hsum
  have hterm : ∀ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 L), 1 ≤ p.ramificationIdx' P * p.inertiaDeg' P := by
    intro P hP
    obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).1 hP
    haveI := hPp; haveI := hPl
    have h1 : 0 < p.ramificationIdx' P := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx p P hp0]
      exact Ideal.ramificationIdx_pos (R := 𝓞 K) P
    have h2 : 0 < p.inertiaDeg' P := Ideal.inertiaDeg'_pos p P
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h1.ne' h2.ne')
  have hpair : ({w.asIdeal, u.asIdeal} : Finset (Ideal (𝓞 L))) ⊆ IsDedekindDomain.primesOverFinset p (𝓞 L) := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact hwmem
    · exact humem
  have hle := Finset.sum_le_sum_of_subset (f := fun P => p.ramificationIdx' P * p.inertiaDeg' P) hpair
  rw [Finset.sum_pair hneI.symm, hsum] at hle
  have hu1 := hterm _ humem
  have hw1 : p.ramificationIdx' w.asIdeal * p.inertiaDeg' w.asIdeal = 1 := by
    have := hterm _ hwmem
    omega
  have he : p.ramificationIdx' w.asIdeal = 1 := Nat.eq_one_of_mul_eq_one_right hw1
  rw [Ideal.ramificationIdx'_eq_ramificationIdx p w.asIdeal hp0] at he
  exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain).2 he

end GlobalTheory.SplitUnram
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CoordinateEmbeddingSplits

section General

variable {G : Type} [Mul G]

def Splits (A : Subalgebra ℂ (G → ℂ)) (p : G → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a b : ι → G → ℂ), (∀ i, a i ∈ A ∧ b i ∈ A) ∧
    ∀ x k, p (x * k) = ∑ i, a i x * b i k

theorem splits_adjoin (S : Set (G → ℂ)) (hS : ∀ p ∈ S, Splits (Algebra.adjoin ℂ S) p) :
    ∀ p ∈ Algebra.adjoin ℂ S, Splits (Algebra.adjoin ℂ S) p := by
  intro p hp
  induction hp using Algebra.adjoin_induction with
  | mem p hp => exact hS p hp
  | algebraMap c =>
    exact ⟨Unit, inferInstance, fun _ => algebraMap ℂ _ c, fun _ => 1,
      fun _ => ⟨Subalgebra.algebraMap_mem _ c, one_mem _⟩, fun x k => by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨ι, _, a, b, hab, h⟩ := hp
    obtain ⟨κ, _, c, d, hcd, h'⟩ := hq
    refine ⟨ι ⊕ κ, inferInstance, Sum.elim a c, Sum.elim b d, ?_, fun x k => ?_⟩
    · rintro (i | i)
      · exact hab i
      · exact hcd i
    · rw [Pi.add_apply, h, h', Fintype.sum_sum_type]
      rfl
  | mul p q _ _ hp hq =>
    obtain ⟨ι, _, a, b, hab, h⟩ := hp
    obtain ⟨κ, _, c, d, hcd, h'⟩ := hq
    refine ⟨ι × κ, inferInstance, fun t => a t.1 * c t.2, fun t => b t.1 * d t.2,
      fun t => ⟨mul_mem (hab _).1 (hcd _).1, mul_mem (hab _).2 (hcd _).2⟩, fun x k => ?_⟩
    rw [Pi.mul_apply, h, h', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.mul_apply]
    ring

theorem Splits.fin {A : Subalgebra ℂ (G → ℂ)} {p : G → ℂ} (h : Splits A p) :
    ∃ (m : ℕ) (a b : Fin m → G → ℂ), (∀ i, a i ∈ A ∧ b i ∈ A) ∧
      ∀ x k, p (x * k) = ∑ i, a i x * b i k := by
  obtain ⟨ι, _, a, b, hab, h⟩ := h
  refine ⟨Fintype.card ι, fun i => a ((Fintype.equivFin ι).symm i), fun i => b ((Fintype.equivFin ι).symm i),
    fun i => hab _, fun x k => ?_⟩
  rw [h]
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm fun i => a i x * b i k).symm

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [NumberField E] [IsCMField E] in
theorem coord_star (τ : E →+* ℂ) (a : Cinf E) : coord τ (star a) = star (coord τ a) := by
  unfold coord
  split_ifs <;> rfl

omit [NumberField E] [IsCMField E] in
theorem continuous_coord (τ : E →+* ℂ) : Continuous (coord τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply (InfinitePlace.mk τ)
  · exact Complex.continuous_conj.comp (continuous_apply (InfinitePlace.mk τ))

omit [NumberField E] [IsCMField E] in
theorem coord_embedding (w : InfinitePlace E) (a : Cinf E) : coord w.embedding a = a w := by
  unfold coord
  rw [InfinitePlace.mk_embedding, if_pos rfl]
  rfl

theorem coord_conjugate (τ : E →+* ℂ) (a : Cinf E) :
    coord (ComplexEmbedding.conjugate τ) a = star (coord τ a) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
      ⟨τ, ComplexEmbedding.isReal_iff.2 h, rfl⟩
  unfold coord
  rw [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (fun h' => hne (h'.symm.trans h))]
    rfl
  · rw [if_pos h, if_neg (fun h' => hne (h.symm.trans h'))]
    exact (star_star _).symm

theorem continuous_pInf : Continuous (pInf E) := by
  have : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)
  exact this.comp continuous_fst

theorem pInf_conj (a : Ad E) : pInf E (conjAd E a) = star (pInf E a) := by
  change (infEq E).symm (infEq E _) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

theorem cEmb_apply (τ : E →+* ℂ) (x : UA E n) (i j : Fin n) :
    (cEmb τ x).val i j = coord τ (pInf E (x.1.val i j)) := rfl

theorem cEmb_inv (τ : E →+* ℂ) (x : UA E n) (i j : Fin n) :
    (cEmb τ x⁻¹).val i j = star ((cEmb τ x).val j i) := by
  have h : (x.1.val.map (conjAd E))ᵀ * 1 * x.1.val = 1 := x.2
  rw [Matrix.mul_one] at h
  have h2 : (x.1⁻¹).val = (x.1.val.map (conjAd E))ᵀ := Units.inv_eq_of_mul_eq_one_left h
  rw [cEmb_apply, cEmb_apply, ← coord_star, ← pInf_conj]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) (Ad E) => coord τ (pInf E (M i j))) h2


variable (E n) in
abbrev coeffs : Set (infU E n → ℂ) :=
  {f | ∃ (τ : E →+* ℂ) (i : Fin n) (j : Fin n), f = fun x : infU E n => (cEmb τ x.val).val i j}

theorem continuous_of_mem (p : infU E n → ℂ) (hp : p ∈ Algebra.adjoin ℂ (coeffs E n)) : Continuous p := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨τ, i, j, rfl⟩ := hp
    have h : Continuous fun x : infU E n => x.1.1.val i j :=
      (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem i j
    exact (continuous_coord τ).comp (continuous_pInf.comp h)
  | algebraMap c => exact continuous_const
  | add p q _ _ hp hq => exact hp.add hq
  | mul p q _ _ hp hq => exact hp.mul hq

theorem star_mem_of_mem (p : infU E n → ℂ) (hp : p ∈ Algebra.adjoin ℂ (coeffs E n)) :
    star p ∈ Algebra.adjoin ℂ (coeffs E n) := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨τ, i, j, rfl⟩ := hp
    exact Algebra.subset_adjoin ⟨ComplexEmbedding.conjugate τ, i, j, funext fun x => (coord_conjugate τ _).symm⟩
  | algebraMap c => exact Subalgebra.algebraMap_mem _ (star c)
  | add p q _ _ hp hq => rw [star_add]; exact add_mem hp hq
  | mul p q _ _ hp hq => rw [star_mul]; exact mul_mem hq hp

theorem separates (x y : infU E n) (hxy : x ≠ y) : ∃ p ∈ Algebra.adjoin ℂ (coeffs E n), p x ≠ p y := by
  by_contra hcon
  refine hxy (Subtype.ext (Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))))
  have h1 : pInf E (x.1.1.val i j) = pInf E (y.1.1.val i j) := by
    funext w
    refine (coord_embedding w _).symm.trans (Eq.trans ?_ (coord_embedding w _))
    by_contra hne
    exact hcon ⟨_, Algebra.subset_adjoin ⟨w.embedding, i, j, rfl⟩, hne⟩
  have hx : GeneralLinearGroup.map (pFin E) x.1.1 = 1 := x.2
  have hy : GeneralLinearGroup.map (pFin E) y.1.1 = 1 := y.2
  have h2 := congrArg (fun g : GL (Fin n) (Af E) => g.val i j) (hx.trans hy.symm)
  exact Prod.ext ((infEq E).symm.injective h1) h2

theorem inv_mem_of_mem (p : infU E n → ℂ) (hp : p ∈ Algebra.adjoin ℂ (coeffs E n)) :
    (fun x => p x⁻¹) ∈ Algebra.adjoin ℂ (coeffs E n) := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨τ, i, j, rfl⟩ := hp
    have h := star_mem_of_mem (E := E) (n := n) _ (Algebra.subset_adjoin ⟨τ, j, i, rfl⟩)
    have e : (fun x : infU E n => (cEmb τ (x⁻¹).val).val i j) =
        star fun x : infU E n => (cEmb τ x.val).val j i := funext fun x => cEmb_inv τ x.1 i j
    exact e ▸ h
  | algebraMap c => exact Subalgebra.algebraMap_mem _ c
  | add p q _ _ hp hq => exact add_mem hp hq
  | mul p q _ _ hp hq => exact mul_mem hp hq

theorem splits_of_mem : ∀ p ∈ Algebra.adjoin ℂ (coeffs E n), Splits (Algebra.adjoin ℂ (coeffs E n)) p := by
  refine splits_adjoin _ ?_
  rintro _ ⟨τ, i, j, rfl⟩
  refine ⟨Fin n, inferInstance, fun l x => (cEmb τ x.val).val i l, fun l x => (cEmb τ x.val).val l j,
    fun l => ⟨Algebra.subset_adjoin ⟨τ, i, l, rfl⟩, Algebra.subset_adjoin ⟨τ, l, j, rfl⟩⟩, fun x k => ?_⟩
  change (cEmb τ (x.val * k.val)).val i j = _
  rw [map_mul, Units.val_mul, Matrix.mul_apply]

theorem main (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    (∀ p ∈ Algebra.adjoin ℂ (coeffs E n), Continuous p) ∧
    (∀ p ∈ Algebra.adjoin ℂ (coeffs E n), star p ∈ Algebra.adjoin ℂ (coeffs E n)) ∧
    (∀ x y : infU E n, x ≠ y → ∃ p ∈ Algebra.adjoin ℂ (coeffs E n), p x ≠ p y) ∧
    (∀ p ∈ Algebra.adjoin ℂ (coeffs E n), (fun x => p x⁻¹) ∈ Algebra.adjoin ℂ (coeffs E n)) ∧
    ∀ p ∈ Algebra.adjoin ℂ (coeffs E n), ∃ (m : ℕ) (a b : Fin m → infU E n → ℂ),
      (∀ i, a i ∈ Algebra.adjoin ℂ (coeffs E n) ∧ b i ∈ Algebra.adjoin ℂ (coeffs E n)) ∧
        ∀ x k : infU E n, p (x * k) = ∑ i, a i x * b i k :=
  ⟨continuous_of_mem, star_mem_of_mem, separates, inv_mem_of_mem, fun p hp => (splits_of_mem p hp).fin⟩

end GlobalTheory.CoordinateEmbeddingSplits

end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

private theorem polyConj_coord_pInf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (τ : E →+* ℂ) (x : E) :
    coord τ (pInf E (algebraMap E (Ad E) x)) = τ x := by
  have h : ∀ w : InfinitePlace E, pInf E (algebraMap E (Ad E) x) w = w.embedding x := fun w => by
    first | exact pInf_algebraMap _ _ | exact pInf_algebraMap _ _ _ | simp [pInf_algebraMap]
  unfold coord
  split_ifs with hτ
  · simp only [Pi.evalRingHom_apply, h, hτ]
  · rcases InfinitePlace.embedding_mk_eq τ with h' | h'
    · exact absurd h' hτ
    · simp [h, h']

theorem exists_cEmb_entry_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {γ : UA E n}
    (hγ : γ ∈ ratU E n) {k : UA E n} (hk : cInf k = cInf γ) (i j : Fin n) :
    ∃ x : E, ∀ τ : E →+* ℂ, (cEmb τ k).val i j = τ x := by
  obtain ⟨γ₀, h₀⟩ := Subgroup.mem_subgroupOf.1 hγ
  refine ⟨γ₀.val i j, fun τ => ?_⟩
  have h1 : (cEmb τ k).val i j = coord τ ((cInf k).val i j) := rfl
  have h2 : (cInf γ).val i j = pInf E ((γ : GA E n).val i j) := rfl
  rw [h1, hk, h2, ← h₀]
  exact polyConj_coord_pInf τ _

theorem exists_conj_polyFun : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ), ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ p' ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∀ γ ∈ ratU E n, ∀ k : infU E n, cInf k.1 = cInf γ → p' k = σ (p k) := by
  intro E _ _ _ n σ p hp
  induction hp using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨τ, i, j, rfl⟩ := hf
    refine ⟨_, Algebra.subset_adjoin ⟨σ.toRingHom.comp τ, i, j, rfl⟩, fun γ hγ k hk => ?_⟩
    obtain ⟨x, hx⟩ := exists_cEmb_entry_eq hγ hk i j
    simp only [hx]
    rfl
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ (σ c), fun _ _ _ _ => rfl⟩
  | add f g _ _ hf hg =>
    obtain ⟨f', hf', hf⟩ := hf
    obtain ⟨g', hg', hg⟩ := hg
    refine ⟨f' + g', add_mem hf' hg', fun γ hγ k hk => ?_⟩
    rw [Pi.add_apply, Pi.add_apply, map_add (f := _), hf γ hγ k hk, hg γ hγ k hk]
  | mul f g _ _ hf hg =>
    obtain ⟨f', hf', hf⟩ := hf
    obtain ⟨g', hg', hg⟩ := hg
    refine ⟨f' * g', mul_mem hf' hg', fun γ hγ k hk => ?_⟩
    rw [Pi.mul_apply, Pi.mul_apply, map_mul, hf γ hγ k hk, hg γ hγ k hk]

end GlobalTheory.UnitaryBC
end

section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem formsTiedSym_chi_zero_finite : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), (∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)) → ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U, (((Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ) :=
  fun D _ _ _ Tf h =>
    GlobalTheory.T.unipotentTypeLevel_character_finiteOrder_rootsOfUnity _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Tf.glev0 D.what₂.LL D.what₂.embLL D.host.g_prime (fun i => (h i).1)

end GlobalTheory
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomKapi


open Formalism.L2.Th1.H in
theorem nsmul_relIdx_mem {V : Type*} [AddCommGroup V] (S M : AddSubgroup V) {z : V} (hz : z ∈ M) :
    relIdx S M • z ∈ S := by
  have h := AddSubgroup.nsmul_index_mem (S.addSubgroupOf M) (⟨z, hz⟩ : M)
  have h2 : ((S.addSubgroupOf M).index • (⟨z, hz⟩ : M) : M).1 ∈ S := AddSubgroup.mem_addSubgroupOf.1 h
  simpa [relIdx, AddSubgroup.relIndex] using h2

theorem denom_prime_to : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ x : Fin 4 → D.host.E, (∀ a, x a ∈ D.host.AA0) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ w, (s : D.host.K) * G (B.γ₀.g x) w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  intro D cc δ B hcc q _ hcop u hn hnq G hG x hx
  set n := Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) with hndef
  set N := Ideal.absNorm cc with hNdef
  have hq : q.Prime := Fact.out
  have hnc : Nat.Coprime n q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hnq).symm
  refine ⟨n * N, Nat.Coprime.mul_left hnc hcop, fun w => ?_⟩
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B

  have hNc : ((N : ℕ) : 𝓞 D.host.K) ∈ cc := Ideal.absNorm_mem cc
  set w₀ : ℂ := δ * D.host.φ₀ (((((N : ℕ) : 𝓞 D.host.K) : D.host.K) : D.host.E)) with hw₀
  have hw₀mem : w₀ ∈ lamOf D cc δ := AddSubgroup.subset_closure ⟨_, hNc, rfl⟩
  have hz : w₀ • emb4 D x ∈ Formalism.L2.Th1.H.pow4 B.lamM := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.gen_mem hw₀mem hx
  have hgC : B.gC (w₀ • emb4 D x) = w₀ • (fun w => D.host.φ₀ ((B.γ₀.g x w : D.host.K) : D.host.E)) := by
    rw [map_smul]
    exact congrArg (w₀ • ·) (B.gC_spec x)
  have hu : u (B.gC (w₀ • emb4 D x)) = w₀ • (fun w => D.host.φ₀ ((G (B.γ₀.g x) w : D.host.K) : D.host.E)) := by
    rw [hgC, map_smul, hG]
  have hM : u (B.gC (w₀ • emb4 D x)) ∈ Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) :=
    ⟨_, ⟨_, hz, rfl⟩, rfl⟩
  have hS := nsmul_relIdx_mem (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) _ hM
  rw [← hndef, hu] at hS
  have hc : n • (w₀ * D.host.φ₀ ((G (B.γ₀.g x) w : D.host.K) : D.host.E)) ∈ B.L.lattice := by
    have := hS w (Set.mem_univ w)
    simpa using this
  obtain ⟨c, -, hc'⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ _ ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B _).1 hc)
  have hC : D.host.φ₀ (((((n * N : ℕ) : D.host.K) * G (B.γ₀.g x) w : D.host.K) : D.host.E)) = D.host.φ₀ ((c : D.host.K) : D.host.E) := by
    apply mul_left_cancel₀ hδ
    rw [← hc', hw₀]
    push_cast
    simp only [map_mul, map_natCast, nsmul_eq_mul]
    ring
  have hK : (((n * N : ℕ) : D.host.K) * G (B.γ₀.g x) w : D.host.K) = (c : D.host.K) :=
    Subtype.coe_injective (D.host.φ₀.injective hC)
  exact ⟨c, hK.symm⟩

end GlobalTheory.MomKapi
end
