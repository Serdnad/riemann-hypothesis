module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
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
import Mathlib.RingTheory.Radical.NatInt
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace BlockAdjoinPrime

variable {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}


open Classical in
def killB (B : Set K) : MRing ι R →ₐ[R] MRing ι R :=
  by
    classical
    exact aeval fun v => if v.1 ∈ B then 0 else X v

def varIdeal (B : Set K) : Ideal (MRing ι R) :=
  Ideal.span {p | ∃ v : Σ k, ι k, v.1 ∈ B ∧ p = X v}

theorem killB_X_of_mem (B : Set K) {v : Σ k, ι k} (hv : v.1 ∈ B) :
    killB (R := R) B (X v) = 0 := by
  classical
  simp [killB, hv]

theorem killB_X_of_not_mem (B : Set K) {v : Σ k, ι k} (hv : v.1 ∉ B) :
    killB (R := R) B (X v) = X v := by
  classical
  simp [killB, hv]

open Classical in
theorem killB_monomial (B : Set K) (d : (Σ k, ι k) →₀ ℕ) (a : R) :
    killB (R := R) B (monomial d a) =
      if ∀ v ∈ d.support, v.1 ∉ B then monomial d a else 0 := by
  rw [killB, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    refine Finsupp.prod_congr fun v hv => ?_
    rw [if_neg (h v hv)]
  · push Not at h
    obtain ⟨v, hv, hB⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero hv, mul_zero]
    rw [if_pos hB, zero_pow (Finsupp.mem_support_iff.mp hv)]

open Classical in
theorem coeff_killB (B : Set K) (p : MRing ι R) (d : (Σ k, ι k) →₀ ℕ) :
    AddMonoidAlgebra.coeff (killB B p) d = if ∀ v ∈ d.support, v.1 ∉ B then AddMonoidAlgebra.coeff p d else 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial e a =>
    rw [killB_monomial]
    by_cases hed : e = d
    · subst hed
      split_ifs <;> simp
    · split_ifs <;> simp [coeff_monomial, hed]
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, hp, hq]
    split_ifs <;> simp

theorem sub_killB_mem (B : Set K) (p : MRing ι R) : p - killB B p ∈ varIdeal (R := R) B := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add (f := _), add_sub_add_comm]
    exact add_mem hp hq
  | mul_X p v hp =>
    have e : p * X v - killB B (p * X v) =
        (p - killB B p) * X v + killB B p * (X v - killB B (X v)) := by
      rw [map_mul]; ring
    rw [e]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    by_cases hv : v.1 ∈ B
    · rw [killB_X_of_mem B hv, sub_zero]
      exact Ideal.subset_span ⟨v, hv, rfl⟩
    · rw [killB_X_of_not_mem B hv, sub_self]
      exact zero_mem _

variable [DecidableEq K]

theorem weight_eq_zero_iff (d : (Σ k, ι k) →₀ ℕ) (B : Set K) :
    (∀ k ∈ B, Finsupp.weight (blockWeight ι) d k = 0) ↔ ∀ v ∈ d.support, v.1 ∉ B := by
  have hw : ∀ k, Finsupp.weight (blockWeight ι) d k =
      ∑ i ∈ d.support, d i * (Pi.single i.1 1 : K → ℕ) k := by
    intro k
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    rfl
  constructor
  · intro h v hv hB
    have h0 := h v.1 hB
    rw [hw, Finset.sum_eq_zero_iff] at h0
    have := h0 v hv
    simp [Finsupp.mem_support_iff.mp hv] at this
  · intro h k hk
    rw [hw, Finset.sum_eq_zero_iff]
    intro i hi
    have hik : i.1 ≠ k := fun e => h i hi (e ▸ hk)
    simp [Ne.symm hik]

theorem killB_mem {Q : Ideal (MRing ι R)} (hQ : IsMultiHomogIdeal Q) (B : Set K)
    {q : MRing ι R} (hq : q ∈ Q) : killB B q ∈ Q := by
  classical
  let M := (q.support.image (Finsupp.weight (blockWeight ι))).filter (fun m => ∀ k ∈ B, m k = 0)
  have key : killB B q = ∑ m ∈ M, weightedHomogeneousComponent (blockWeight ι) m q := by
    ext d
    rw [coeff_killB, coeff_sum]
    simp_rw [coeff_weightedHomogeneousComponent]
    rw [Finset.sum_ite_eq]
    by_cases hd : AddMonoidAlgebra.coeff q d = 0
    · simp [hd]
    · have hmem : d ∈ q.support := mem_support_iff.mpr hd
      have hiff : Finsupp.weight (blockWeight ι) d ∈ M ↔ ∀ v ∈ d.support, v.1 ∉ B := by
        rw [← weight_eq_zero_iff]
        simp only [M, Finset.mem_filter, Finset.mem_image]
        exact ⟨fun h => h.2, fun h => ⟨⟨d, hmem, rfl⟩, h⟩⟩
      by_cases hP : ∀ v ∈ d.support, v.1 ∉ B
      · rw [if_pos hP, if_pos (hiff.mpr hP)]
      · rw [if_neg hP, if_neg (fun h => hP (hiff.mp h))]
  rw [key]
  exact Q.sum_mem fun m _ => hQ q hq m

theorem sup_eq_comap {Q : Ideal (MRing ι R)} (hQ : IsMultiHomogIdeal Q) (B : Set K) :
    Q ⊔ varIdeal B = Q.comap (killB B) := by
  apply le_antisymm
  · refine sup_le (fun q hq => killB_mem hQ B hq) ?_
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨v, hv, rfl⟩
    show killB B (X v) ∈ Q
    rw [killB_X_of_mem B hv]
    exact zero_mem _
  · intro p hp
    have : p = killB B p + (p - killB B p) := by ring
    rw [this]
    exact add_mem (Ideal.mem_sup_left hp) (Ideal.mem_sup_right (sub_killB_mem B p))

theorem proof : BlockAdjoinPrime.Statement := by
  intro R _ K _ _ ι Q B hP hQ
  have h := sup_eq_comap (R := R) hQ B
  change (Q ⊔ varIdeal B).IsPrime ∧ ∀ v : Σ k, ι k, v.1 ∉ B → (X v ∈ Q ⊔ varIdeal B ↔ X v ∈ Q)
  rw [h]
  refine ⟨Ideal.IsPrime.comap (killB B) (hK := hP), fun v hv => ?_⟩
  rw [Ideal.mem_comap, killB_X_of_not_mem B hv]

end BlockAdjoinPrime

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

namespace DegLTEventuallyConst

theorem eq_of_unitSteps_eq_zero {K : Type} [Fintype K] [DecidableEq K] (g : (K → ℤ) → ℤ)
    (N : K → ℤ) (h : ∀ m, N ≤ m → ∀ k, g m - g (m - Pi.single k 1) = 0) :
    ∀ d : ℕ, ∀ m, N ≤ m → ∑ k, (m k - N k).toNat = d → g m = g N := by
  intro d
  induction d with
  | zero =>
    intro m hm hs
    have hmN : m = N := by
      funext k
      have hk : (m k - N k).toNat = 0 := (Finset.sum_eq_zero_iff.mp hs) k (Finset.mem_univ k)
      have hle : N k ≤ m k := hm k
      omega
    rw [hmN]
  | succ d ih =>
    intro m hm hs
    obtain ⟨k, -, hk⟩ : ∃ k ∈ Finset.univ, (m k - N k).toNat ≠ 0 := by
      by_contra hne
      push Not at hne
      rw [Finset.sum_eq_zero hne] at hs
      omega
    obtain ⟨m', hm'⟩ : ∃ m' : K → ℤ, m' = m - Pi.single k (1 : ℤ) := ⟨_, rfl⟩
    have hm'k : m' k = m k - 1 := by simp [hm']
    have hm'j : ∀ j, j ≠ k → m' j = m j := by
      intro j hj
      simp [hm', hj]
    have hkk : N k + 1 ≤ m k := by omega
    have hNm' : N ≤ m' := by
      intro j
      show N j ≤ m' j
      by_cases hj : j = k
      · rw [hj, hm'k]
        omega
      · rw [hm'j j hj]
        exact hm j
    have hs' : ∑ j, (m' j - N j).toNat = d := by
      have e1 := Finset.add_sum_erase Finset.univ (fun j => (m j - N j).toNat) (Finset.mem_univ k)
      have e2 := Finset.add_sum_erase Finset.univ
        (fun j => (m' j - N j).toNat) (Finset.mem_univ k)
      have e3 : ∑ j ∈ Finset.univ.erase k, (m' j - N j).toNat =
          ∑ j ∈ Finset.univ.erase k, (m j - N j).toNat :=
        Finset.sum_congr rfl fun j hj => by rw [hm'j j (Finset.ne_of_mem_erase hj)]
      simp only [hm'k] at e2
      omega
    have step : g m - g m' = 0 := by rw [hm']; exact h m hm k
    rw [← ih _ hNm' hs']
    omega

theorem proof (h1 : MixedDiffLinear.Statement) : DegLTEventuallyConst.Statement := by
  intro K _ _ n f hf bs
  have hev : ∀ k : K, ∀ᶠ m in Filter.atTop,
      mixedDiff bs f m - mixedDiff bs f (m - Pi.single k 1) = 0 := by
    intro k
    have hk := hf (Matrix.vecCons (Pi.single k 1) bs)
    rw [(h1 K n bs f 0 0 0 (Pi.single k 1)).2.2.2.2] at hk
    exact hk
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Filter.eventually_all.mpr hev)
  exact ⟨mixedDiff bs f N, Filter.eventually_atTop.mpr ⟨N, fun m hm =>
    eq_of_unitSteps_eq_zero (mixedDiff bs f) N (fun m hm => hN m hm) _ m hm rfl⟩⟩

end DegLTEventuallyConst

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem length_localizedModule_eq_of_surjective {S T : Type*} [CommRing S] [CommRing T]
    (π : S →+* T) (hπ : Function.Surjective π) (Q : Ideal T) [Q.IsPrime] (W : Ideal S) [W.IsPrime]
    (hW : W = Q.comap π) (M N : Type*) [AddCommGroup M] [Module S M] [AddCommGroup N] [Module T N]
    (e : M ≃+ N) (he : ∀ (s : S) (x : M), e (s • x) = π s • e x) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M) =
      Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl N) := by
  let φ : Localization.AtPrime W →+* Localization.AtPrime Q := Localization.localRingHom W Q π hW
  have hmem : ∀ s : S, s ∈ W.primeCompl ↔ π s ∈ Q.primeCompl := fun s => by
    subst hW; rfl
  have hφ : ∀ s : S, φ (algebraMap S _ s) = algebraMap T _ (π s) :=
    Localization.localRingHom_to_map W Q π hW
  have hsurj : Function.Surjective φ := by
    intro b
    obtain ⟨⟨t, u⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl b
    obtain ⟨s, rfl⟩ := hπ t
    obtain ⟨v, hv⟩ := hπ u
    refine ⟨IsLocalization.mk' _ s (⟨v, (hmem v).2 (hv ▸ u.2)⟩ : W.primeCompl), ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hv
  let _ : Algebra (Localization.AtPrime W) (Localization.AtPrime Q) := φ.toAlgebra
  let _ : Module (Localization.AtPrime W) (LocalizedModule Q.primeCompl N) := Module.compHom _ φ
  have _ : IsScalarTower (Localization.AtPrime W) (Localization.AtPrime Q)
      (LocalizedModule Q.primeCompl N) :=
    ⟨fun a b n => mul_smul (φ a) b n⟩
  let _ : Module S (LocalizedModule Q.primeCompl N) := Module.compHom _ (φ.comp (algebraMap S _))
  have _ : IsScalarTower S (Localization.AtPrime W) (LocalizedModule Q.primeCompl N) :=
    ⟨fun s a n => by
      show φ (s • a) • n = φ (algebraMap S _ s) • (φ a • n)
      rw [Algebra.smul_def, map_mul, mul_smul]⟩
  have hsmul : ∀ (s : S) (y : LocalizedModule Q.primeCompl N), s • y = π s • y := fun s y => by
    show φ (algebraMap S _ s) • y = _
    rw [hφ, algebraMap_smul]
  let g : M →ₗ[S] LocalizedModule Q.primeCompl N :=
    { toFun := fun x => LocalizedModule.mkLinearMap Q.primeCompl N (e x)
      map_add' := fun x y => by simp only [map_add (f := _)]
      map_smul' := fun s x => by
        rw [RingHom.id_apply, hsmul, he, LinearMap.map_smul] }
  have hg : IsLocalizedModule W.primeCompl g := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ?_⟩
    · have hu : IsUnit (φ (algebraMap S _ (s : S))) :=
        (IsLocalization.map_units (Localization.AtPrime W) s).map φ
      rw [Module.End.isUnit_iff]
      refine ⟨fun y z h => ?_, fun y => ⟨((hu.unit⁻¹ : (Localization.AtPrime Q)ˣ) :
        Localization.AtPrime Q) • y, ?_⟩⟩
      · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply] at h
        exact hu.smul_left_cancel.mp h
      · rw [Module.algebraMap_end_apply]
        show φ (algebraMap S _ (s : S)) • _ = y
        rw [← mul_smul, hu.mul_val_inv, one_smul]
    · induction y using LocalizedModule.induction_on with
      | h n t =>
      obtain ⟨s, hs⟩ := hπ t
      refine ⟨(e.symm n, ⟨s, (hmem s).2 (hs ▸ t.2)⟩), ?_⟩
      show s • LocalizedModule.mk n t = LocalizedModule.mk (e (e.symm n)) 1
      rw [hsmul, hs, AddEquiv.apply_symm_apply, LocalizedModule.smul'_mk]
      exact LocalizedModule.mk_cancel t n
    · have h' : LocalizedModule.mk (e x₁) (1 : Q.primeCompl) = LocalizedModule.mk (e x₂) 1 := h
      obtain ⟨c, hc⟩ := LocalizedModule.mk_eq.mp h'
      obtain ⟨s, hs⟩ := hπ c
      refine ⟨⟨s, (hmem s).2 (hs ▸ c.2)⟩, e.injective ?_⟩
      show e (s • x₁) = e (s • x₂)
      rw [he, he, hs]
      simpa [Submonoid.smul_def] using hc
  let eA := (IsLocalizedModule.iso W.primeCompl g).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)
  rw [eA.length_eq]
  exact Module.length_eq_of_surjective hsurj

theorem SpecialMultAt.proof : SpecialMultAt.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P W _ hW _
  let π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O)
  have hspec : ∀ I : Ideal (MRing ι O), specialIdeal I = I.map π := fun _ => rfl
  have hπ : Function.Surjective π := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π = Ideal.span {C ϖ} := by
    rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hcm : ∀ I : Ideal (MRing ι O), (specialIdeal I).comap π = I ⊔ Ideal.span {C ϖ} := by
    intro I
    rw [hspec, Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, hker]
  have hWc : W = (specialIdeal W).comap π := by
    rw [hcm]
    exact (sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hW))).symm
  let f : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.Quotient.mk _).comp π
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hπ
  have hkerf : RingHom.ker f = P ⊔ Ideal.span {C ϖ} := by
    rw [← hcm]
    ext x
    simp [f, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  let e := ((Ideal.quotEquivOfEq hkerf.symm).trans (RingHom.quotientKerEquivOfSurjective hf))
  have hemk : ∀ z, e (Ideal.Quotient.mk _ z) = f z := fun z => rfl
  have he : ∀ (s : MRing ι O) (x : MRing ι O ⧸ (P ⊔ Ideal.span {C ϖ})),
      e.toAddEquiv (s • x) = π s • e.toAddEquiv x := by
    intro s x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, hemk]
    simp [f]
    rw [← map_mul]
    rfl
  exact length_localizedModule_eq_of_surjective π hπ (specialIdeal W) W hWc _ _ e.toAddEquiv he

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem SpecialCycleEval.proof (h1 : SpecialIdealCorresp.Statement.{u})
    (h2 : SpecialIdealSurj.Statement.{u}) (h3 : SpecialMultAt.Statement.{u}) :
    SpecialCycleEval.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P n
  classical
  let s : Set (Ideal (MRing ι O)) :=
    {W | W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ∧ IsRelevant W}
  let t : Set (Ideal (MRing ι (IsLocalRing.ResidueField O))) :=
    {V | V ∈ (specialIdeal P).minimalPrimes ∧ IsRelevant V}
  have hsupp1 : Function.support (fun W => divCycle P (C ϖ) W * n (specialIdeal W)) ⊆ s := by
    intro W hW
    by_contra h
    apply hW
    show divCycle P (C ϖ) W * n (specialIdeal W) = 0
    have h' : ¬ (W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ∧ IsRelevant W) := h
    unfold divCycle
    rw [dite_eq_right h', zero_mul]
  have hsupp2 : Function.support (fun V => idealCycle (specialIdeal P) V * n V) ⊆ t := by
    intro V hV
    by_contra h
    apply hV
    show idealCycle (specialIdeal P) V * n V = 0
    have h' : ¬ (V ∈ (specialIdeal P).minimalPrimes ∧ IsRelevant V) := h
    unfold idealCycle
    rw [dite_eq_right h', zero_mul]
  have hmem : ∀ W ∈ s, W.IsPrime ∧ (C ϖ : MRing ι O) ∈ W := fun W hW =>
    ⟨hW.1.1.1, hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))⟩
  have hmaps : ∀ W ∈ s, specialIdeal W ∈ t := by
    intro W hW
    obtain ⟨hp, hc⟩ := hmem W hW
    obtain ⟨-, hmin, hrel, -⟩ := h1 O ϖ hϖ K ι P W hp hc
    exact ⟨hmin.mp hW.1, hrel.mp hW.2⟩
  have e1 : (∑ᶠ W, divCycle P (C ϖ) W * n (specialIdeal W)) =
      ∑ᶠ W ∈ s, divCycle P (C ϖ) W * n (specialIdeal W) := by
    rw [finsum_mem_def, Set.indicator_eq_self.mpr hsupp1]
  have e2 : (∑ᶠ V, idealCycle (specialIdeal P) V * n V) =
      ∑ᶠ V ∈ t, idealCycle (specialIdeal P) V * n V := by
    rw [finsum_mem_def, Set.indicator_eq_self.mpr hsupp2]
  show (∑ᶠ W, divCycle P (C ϖ) W * n (specialIdeal W)) =
    ∑ᶠ V, idealCycle (specialIdeal P) V * n V
  rw [e1, e2]
  refine finsum_mem_eq_of_bijOn specialIdeal ⟨hmaps, ?_, ?_⟩ ?_
  · intro W hW W' hW' heq
    obtain ⟨hp, hc⟩ := hmem W hW
    obtain ⟨hp', hc'⟩ := hmem W' hW'
    exact ((h1 O ϖ hϖ K ι P W hp hc).2.2.2 W' hp' hc' heq.symm).symm
  · intro V hV
    have hVp : V.IsPrime := hV.1.1.1
    obtain ⟨W, hWp, hc, rfl⟩ := h2 O ϖ hϖ K ι V hVp
    obtain ⟨-, hmin, hrel, -⟩ := h1 O ϖ hϖ K ι P W hWp hc
    exact ⟨W, ⟨hmin.mpr hV.1, hrel.mpr hV.2⟩, rfl⟩
  · intro W hW
    obtain ⟨hp, hc⟩ := hmem W hW
    have := hp
    have := (h1 O ϖ hϖ K ι P W hp hc).1
    have hm := h3 O ϖ hϖ K ι P W hc
    congr 1
    unfold divCycle idealCycle
    have hW' : W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ∧ IsRelevant W := hW
    have hV' : specialIdeal W ∈ (specialIdeal P).minimalPrimes ∧ IsRelevant (specialIdeal W) :=
      hmaps W hW
    rw [dite_eq_left hW', dite_eq_left hV']
    exact congrArg (fun x : ℕ∞ => ((x.toNat : ℕ) : ℤ)) hm

end GroundTheory.Heights₂.Heights.NumbersDVR
end
