module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle004
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle125
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open PowerSeries GlobalTheory.BK
open scoped NormedField Valued

noncomputable section

namespace GlobalTheory.ZFin

theorem isDomain_isPrincipalIdealRing (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] : IsDomain O ∧ IsPrincipalIdealRing O := by
  have hl : ‖(l : K)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap']
    exact_mod_cast Padic.norm_p_lt_one
  have hl0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  letI : NontriviallyNormedField K :=
    { ‹NormedField K› with
      non_trivial := ⟨(l : K)⁻¹, by
        rw [norm_inv]; exact one_lt_inv₀ (norm_pos_iff.2 hl0) |>.2 hl⟩ }
  haveI : ProperSpace K := FiniteDimensional.proper ℚ_[l] K
  haveI : CompactSpace 𝒪[K] := by
    have h1 : ((𝒪[K] : Set K)) = Metric.closedBall 0 1 := by
      ext x; simp [Valued.integer.mem_iff]
    have h2 : IsCompact ((𝒪[K] : Set K)) := h1 ▸ isCompact_closedBall 0 1
    exact (isCompact_iff_compactSpace (s := (𝒪[K] : Set K))).1 h2
  haveI : IsPrincipalIdealRing 𝒪[K] := Valued.integer.isPrincipalIdealRing_of_compactSpace
  let f : O →+* 𝒪[K] :=
    { toFun := fun x => ⟨algebraMap O K x, Valued.integer.mem_iff.2 ((IsUnitBall.mem_range_iff _).1 ⟨x, rfl⟩)⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => IsUnitBall.inj (O := O) (K := K) (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := (IsUnitBall.mem_range_iff (O := O) (y : K)).2 (Valued.integer.mem_iff.1 y.2)
    exact ⟨x, Subtype.ext hx⟩
  let g := RingEquiv.ofBijective f hf
  haveI : IsDomain O := (IsUnitBall.inj (O := O) (K := K)).isDomain (algebraMap O K)
  exact ⟨inferInstance, IsPrincipalIdealRing.of_surjective (g.symm : 𝒪[K] →+* O) g.symm.surjective⟩

theorem exists_eq_add_E_pow_mul (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [NeZero e] (n : ℕ) (f : K⟦X⟧) (hf : f ∈ A O K) :
    ∃ (c : Fin (e * n) → O) (g : K⟦X⟧), g ∈ A O K ∧
      f = ∑ k : Fin (e * n), C (algebraMap O K (c k)) * X ^ (k : ℕ) + E K l e ^ n * g :=
  GlobalTheory.T.weierstrass_division_eisensteinPow_integral O K l e n f hf

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]


variable (K l e a ι) in
def gen (η : ℕ) (p : ZMod a × ι × Fin (e * η)) : Vec K a ι :=
  Pi.single p.1 (Pi.single p.2.1 (Ezpow K l e (-η) * X ^ (p.2.2 : ℕ)))

theorem gen_mem (P : PhiMod O K l e a ι) (η : ℕ) (p : ZMod a × ι × Fin (e * η)) :
    gen K l e a ι η p ∈ P.EM η := by
  rw [mem_divE]
  refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul, gen]
  by_cases hτ : τ = p.1
  · subst hτ
    rw [Pi.single_eq_same]
    by_cases hi : i = p.2.1
    · subst hi
      rw [Pi.single_eq_same, ← mul_assoc, E_pow_mul_Ezpow_neg, one_mul]
      exact pow_mem HasU.X_mem _
    · rw [Pi.single_eq_of_ne hi, mul_zero]; exact zero_mem _
  · rw [Pi.single_eq_of_ne hτ]; simp

theorem sum_gen_apply (η : ℕ) (c : ZMod a × ι × Fin (e * η) → O) (τ : ZMod a) (i : ι) :
    (∑ p, c p • gen K l e a ι η p) τ i =
      Ezpow K l e (-η) * ∑ k : Fin (e * η), C (algebraMap O K (c (τ, i, k))) * X ^ (k : ℕ) := by
  simp only [Finset.sum_apply, Pi.smul_apply, gen, Fintype.sum_prod_type, Finset.mul_sum]
  simp only [Pi.single_apply, ite_apply, Pi.zero_apply, smul_ite, smul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx]), Fintype.sum_eq_single i
    (fun x hx => by simp [Ne.symm hx])]
  simp only [if_true]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← algebraMap_smul K⟦X⟧ (c (τ, i, k)), algebraMap_eq_C, smul_eq_mul, mul_left_comm]

theorem finite_quot (P : PhiMod O K l e a ι) (η : ℕ) :
    Module.Finite O ((P.EM η).restrictScalars O ⧸
      (P.M.restrictScalars O).submoduleOf ((P.EM η).restrictScalars O)) := by
  let F : (ZMod a × ι × Fin (e * η) → O) →ₗ[O] (P.EM η).restrictScalars O :=
    LinearMap.codRestrict _ (Fintype.linearCombination O (gen K l e a ι η)) fun c => by
      rw [Fintype.linearCombination_apply]
      exact sum_mem fun p _ => Submodule.smul_mem _ _ (gen_mem P η p)
  refine Module.Finite.of_surjective ((Submodule.mkQ _).comp F) fun q => ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hy2 : E K l e ^ η • y ∈ P.M := hy
  have hyA (τ : ZMod a) (i : ι) : E K l e ^ η * y τ i ∈ A O K := by
    have := mem_vecs.1 (mem_tot.1 hy2 τ) i
    simpa using this
  choose c g hg hfg using fun τ i => exists_eq_add_E_pow_mul O K l e η _ (hyA τ i)
  refine ⟨fun p => c p.1 p.2.1 p.2.2, ?_⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  change (∑ p, c p.1 p.2.1 p.2.2 • gen K l e a ι η p) - y ∈ P.M
  refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
  rw [Pi.sub_apply, Pi.sub_apply, sum_gen_apply]
  have hy' : y τ i = Ezpow K l e (-η) * (E K l e ^ η * y τ i) := by
    rw [← mul_assoc, mul_comm (Ezpow K l e (-η)), E_pow_mul_Ezpow_neg, one_mul]
  dsimp only
  rw [hy', hfg τ i, mul_add, sub_add_cancel_left, ← mul_assoc,
    mul_comm (Ezpow K l e (-η)) (E K l e ^ η), E_pow_mul_Ezpow_neg, one_mul]
  exact neg_mem (hg τ i)

variable [TameDescentExponentData K l e a]

theorem finite_Z {η H : ℕ} (D : BKDat O K l e a ι η H) : Module.Finite O D.Z := by
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (l := l) (e := e) (a := a)
  obtain ⟨_, _⟩ := isDomain_isPrincipalIdealRing O K l
  haveI := finite_quot D.toPhiMod η
  exact Module.Finite.equiv (D.desc.quotInvEquiv η)

theorem free_Z {η H : ℕ} (D : BKDat O K l e a ι η H) : Module.Free O D.Z := by
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (l := l) (e := e) (a := a)
  obtain ⟨_, _⟩ := isDomain_isPrincipalIdealRing O K l
  haveI := finite_Z D
  haveI : NoZeroSMulDivisors O D.Z := ⟨fun {c w} h => by
    have h1 : c • (w : D.Pol) = 0 := congrArg Subtype.val h
    rw [← algebraMap_smul K c] at h1
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl (IsUnitBall.inj (O := O) (K := K) (by rw [h2, map_zero]))
    · exact Or.inr (Subtype.ext h2)⟩
  exact Module.free_of_finite_type_torsion_free'

theorem exists_pow_smul_mem_range {η H : ℕ} (D : BKDat O K l e a ι η H) (w : D.Pol) :
    w ∈ D.PolEta η ↔
      ∃ n : ℕ, (l : K) ^ n • w ∈ LinearMap.range (Descent.quotToPol D.toPhiMod η) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ D.Mext (RpiE O K l e) := mem_tot.2 fun τ => mem_vecs.2 fun i => ⟨η, by
      have := mem_vecs.1 (mem_tot.1 hy τ) i
      simpa using this⟩
    obtain ⟨v, hv, hd⟩ := D.exists_sub_hatTot_mem_Mhat η ((D.smul_hatTot_mem_Mhat_iff η hy').2 hy)
    have hv' : v ∈ D.Mext (RpiE O K l e) := mem_tot.2 fun τ => mem_vecs.2 fun i => ⟨η, by
      have := invL_A_le_Rpi l e (mem_vecs.1 (mem_tot.1 hv τ) i)
      simpa using this⟩
    have hcls := (D.hatTot_sub_mem_Mhat_iff hy' hv').1 hd
    have hl (n : ℕ) (f : K⟦X⟧) : (l : K) ^ n • f = ((l : A O K) : K⟦X⟧) ^ n * f := by
      simp [smul_eq_C_mul]
    choose n hn using fun p : ZMod a × ι => mem_tot.1 hv p.1 p.2
    refine ⟨Finset.univ.sup n, Submodule.Quotient.mk ⟨(l : K) ^ Finset.univ.sup n • v, ?_⟩, ?_⟩
    · refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
      obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i)))
      rw [smul_comm, Pi.smul_apply, Pi.smul_apply, hl, hc, pow_add, mul_assoc]
      exact mul_mem (pow_mem (l : A O K).2 c) (hn (τ, i))
    · change D.cls ((l : K) ^ Finset.univ.sup n • v) = (l : K) ^ Finset.univ.sup n • D.cls y
      rw [map_smul, hcls]
  · rintro ⟨n, q, hq⟩
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have h1 : (l : K) ^ n • w ∈ D.PolEta η := by
      rw [← hq]
      exact D.cls_mem_PolEta hy
    have h2 := (D.PolEta η).smul_mem ((l : K) ^ n)⁻¹ h1
    rwa [inv_smul_smul₀ (pow_ne_zero n (l_ne_zero (K := K) l))] at h2

theorem mem_Zl_iff {η H : ℕ} (D : BKDat O K l e a ι η H) (w : D.Pol) :
    w ∈ D.Zl ↔ ∃ n : ℕ, (l : K) ^ n • w ∈ D.Z := by
  constructor
  · rintro ⟨hw1, hw2⟩
    obtain ⟨n, q, hq⟩ := (exists_pow_smul_mem_range D w).1 hw1
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨n, D.desc.mem_Z.2 ⟨⟨y, hy, hq⟩, fun g => ?_⟩⟩
    rw [map_smul, hw2 g]
  · rintro ⟨n, hn⟩
    have h2 := D.Zl.smul_mem ((l : K) ^ n)⁻¹ (D.desc.mem_Zl_of_mem_Z hn)
    rwa [inv_smul_smul₀ (pow_ne_zero n (l_ne_zero (K := K) l))] at h2

end GlobalTheory.ZFin


open GlobalTheory.ZFin in
theorem GlobalTheory.ZFin.finiteFree_and_localisation : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ)
    (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.FiniteFree D ∧ GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Localisation D := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D
  exact ⟨⟨free_Z D, finite_Z D⟩, Descent.quotToPol_injective (P := D.toPhiMod) η,
    fun w => exists_pow_smul_mem_range D w, D.desc.map_invariants_actQuot η, fun w => mem_Zl_iff D w⟩
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.BlockJumpsCompare

section Continuity

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [IsTopologicalRing O] {X : Type} [TopologicalSpace X]

theorem continuous_of_mul (had : IsAdic (IsLocalRing.maximalIdeal O)) {d : O} (hd : d ≠ 0) {f : X → O}
    (h : Continuous fun x => d * f x) : Continuous f := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hp
  have hm : ∀ (n : ℕ) (y : O), y ∈ (IsLocalRing.maximalIdeal O) ^ n ↔ p ^ n ∣ y := by
    intro n y
    rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rw [continuous_iff_continuousAt]
  intro x₀
  have h0 : Filter.Tendsto (fun x => (u : O) * p ^ k * (f x - f x₀)) (nhds x₀) (nhds 0) := by
    have := (h.sub (continuous_const (y := (u : O) * p ^ k * f x₀))).tendsto x₀
    simpa [mul_sub, Pi.sub_def] using this
  have h1 : Filter.Tendsto (fun x => f x - f x₀) (nhds x₀) (nhds 0) := by
    rw [had.hasBasis_nhds_zero.tendsto_right_iff] at h0 ⊢
    intro n _
    filter_upwards [h0 (k + n) trivial] with x hx
    have hx' := (hm _ _).1 hx
    refine (hm _ _).2 ?_
    rw [pow_add, mul_assoc, Units.dvd_mul_left] at hx'
    exact (mul_dvd_mul_iff_left (pow_ne_zero k hp.ne_zero)).1 hx'
  simpa [ContinuousAt] using h1.add_const (f x₀)

theorem continuous_of_comb (had : IsAdic (IsLocalRing.maximalIdeal O)) {ι : Type} [Fintype ι]
    (c : ι → FractionRing O) {h : ι → X → O} (hh : ∀ j, Continuous (h j)) {f : X → O}
    (hf : ∀ x, algebraMap O (FractionRing O) (f x) =
      ∑ j, c j * algebraMap O (FractionRing O) (h j x)) : Continuous f := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) c
  choose a ha using hd
  refine continuous_of_mul had (nonZeroDivisors.ne_zero d.2) ?_
  have : (fun x => (d : O) * f x) = fun x => ∑ j, a j * h j x := by
    funext x
    apply IsFractionRing.injective O (FractionRing O)

    simp only [map_mul, map_sum, hf, ha, Finset.mul_sum, Algebra.smul_def, mul_assoc]
  rw [this]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (hh j)

theorem continuous_of_splitsAs (had : IsAdic (IsLocalRing.maximalIdeal O)) {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] {n r t : ℕ} {M : Γ →* Matrix (Fin n) (Fin n) O}
    {P : Γ →* Matrix (Fin r) (Fin r) O} {χ : Fin t → Γ → FractionRing O}
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps.SplitsAs (mapM (algebraMap O (FractionRing O)) M)
      (mapM (algebraMap O (FractionRing O)) P) χ)
    (hM : Continuous fun g => M g) : Continuous fun g => P g := by
  obtain ⟨e, he⟩ := hs
  refine continuous_matrix fun a b => ?_
  set u : Fin n → FractionRing O := e.symm (Pi.single b 1, 0) with hu
  refine continuous_of_comb had
    (fun jk : Fin n × Fin n => (e (Pi.single jk.1 1)).1 a * u jk.2)
    (h := fun jk g => M g jk.1 jk.2) (fun jk => hM.matrix_elem jk.1 jk.2) fun g => ?_
  have h1 := congrFun (congrArg Prod.fst (he g u)) a
  have h2 : ∀ v : Fin n → FractionRing O, (e v).1 a = ∑ j, (e (Pi.single j 1)).1 a * v j := by
    intro v
    conv_lhs => rw [pi_eq_sum_univ' v]

    simp [map_sum, Prod.fst_sum, Finset.sum_apply, mul_comm]
  rw [h2] at h1
  simp only [hu, LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one] at h1
  rw [← hu] at h1
  rw [Fintype.sum_prod_type]
  refine Eq.trans ?_ (h1.symm.trans ?_)
  · rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ * (algebraMap O (FractionRing O) (M g j k) * u k) = _
    ring

end Continuity

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

theorem blockSum_iff (π : N.X i) :
    GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum N i r ρ π ↔ GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps.BlockSplit N i r ρ π := Iff.rfl

theorem continuous_rho (π : N.X i) (hr : IsHeckeGalois N i π (r π))
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum N i r ρ π) :
    Continuous (fun g => ((ρ π g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) :=
  continuous_of_splitsAs (M := rO N i r π) (P := rhoO N i ρ π) (N.O_adic i)
    ((blockSum_iff N i r ρ π).1 hs) hr.1

end Glob

end GlobalTheory.BlockJumpsCompare

end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspRep

theorem cornerGL_apply_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) (i j : Fin a) :
    (cornerGL a s g).val i j = (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j) :=
  rfl

theorem cornerGL_apply_ne_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {i j : Fin a} (h : i ≠ j) :
    (cornerGL a s g).val i j = s (g.val i j) := by
  rw [cornerGL_apply_loctri]
  simp [Matrix.one_apply_ne h]

theorem cornerGL_apply_diag_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {j : Fin a} (h : g.val j j = 1) :
    (cornerGL a s g).val j j = 1 := by
  rw [cornerGL_apply_loctri, h]
  simp

theorem locTri_adelic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin a) (w.adicCompletion E)), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) → (∀ i j : Fin a, j < i → (finGL E a (locGL E a w u)).val i j = 0) ∧ (∀ j : Fin a, (finGL E a (locGL E a w u)).val j j = 1) ∧ ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (finGL E a (locGL E a w u)).val p.1 p.2 = sFin E (sLoc E w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2)) := by
  intro E _ _ _ a w u hlow hdiag
  have hoff : ∀ i j : Fin a, i ≠ j → (finGL E a (locGL E a w u)).val i j = sFin E (sLoc E w (u.val i j)) := by
    intro i j h
    rw [finGL, cornerGL_apply_ne_loctri _ _ h, locGL, cornerGL_apply_ne_loctri _ _ h]
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    rw [hoff i j (ne_of_gt h), hlow i j h, map_zero, map_zero]
  · intro j
    exact cornerGL_apply_diag_loctri _ _ (cornerGL_apply_diag_loctri _ _ (hdiag j))

  · rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.mp hp).2
    have hne : p.1 ≠ p.2 := by
      intro h; rw [h] at hp'; omega
    exact hoff p.1 p.2 hne

end GlobalTheory.CuspRep
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.TiltAbs

variable {l : ℕ} [Fact l.Prime]

lemma rootT_pow (x : Per.Fl l) (n : ℕ) : rootT x n ^ l ^ n = x.untilt :=
  PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n

lemma untilt_add (x y : Per.Fl l) :
    ∃ t : Per.OC l, (x + y).untilt = x.untilt + y.untilt + (l : Per.OC l) * t := by
  have h : Ideal.Quotient.mk (Ideal.span {(l : Per.OC l)}) (x + y).untilt =
      Ideal.Quotient.mk (Ideal.span {(l : Per.OC l)}) (x.untilt + y.untilt) := by
    rw [PreTilt.mk_untilt_eq_coeff_zero, map_add (f := _), map_add (f := _), PreTilt.mk_untilt_eq_coeff_zero,
      PreTilt.mk_untilt_eq_coeff_zero]
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by rw [← ht]; ring⟩

lemma rootT_add (x y : Per.Fl l) (n : ℕ) :
    ∃ t : Per.OC l, rootT (x + y) n = rootT x n + rootT y n + (l : Per.OC l) * t := by
  unfold rootT
  rw [iterate_map_add]
  exact untilt_add _ _

lemma norm_le_one (t : Per.OC l) : ‖(t : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 t.2

lemma norm_l_lt : ‖((l : ℕ) : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt

lemma bound (x y : Per.Fl l) (n : ℕ) :
    ‖(((x + y).untilt : Per.OC l) : ℂ_[l])‖ ≤
      max (max ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ‖((y.untilt : Per.OC l) : ℂ_[l])‖)
        (‖((l : ℕ) : ℂ_[l])‖ ^ l ^ n) := by
  obtain ⟨t, ht⟩ := rootT_add x y n
  rw [← rootT_pow (x + y) n, ← rootT_pow x n, ← rootT_pow y n]
  have h1 : ‖((rootT (x + y) n : Per.OC l) : ℂ_[l])‖ ≤
      max (max ‖((rootT x n : Per.OC l) : ℂ_[l])‖ ‖((rootT y n : Per.OC l) : ℂ_[l])‖)
        ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [ht]
    push_cast
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max
      (IsUltrametricDist.norm_add_le_max _ _) ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one t)
  push_cast
  simp only [norm_pow]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 (l ^ n)
  refine h2.trans ?_
  rcases max_choice (max ‖((rootT x n : Per.OC l) : ℂ_[l])‖ ‖((rootT y n : Per.OC l) : ℂ_[l])‖)
    ‖((l : ℕ) : ℂ_[l])‖ with h | h <;> rw [h]
  · refine le_trans ?_ (le_max_left _ _)
    rcases max_choice ‖((rootT x n : Per.OC l) : ℂ_[l])‖ ‖((rootT y n : Per.OC l) : ℂ_[l])‖
      with h | h <;> rw [h]
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact le_max_right _ _

lemma eq_zero_of_untilt (x : Per.Fl l) (hx : x.untilt = 0) : x = 0 := by
  apply Perfection.ext
  intro n
  have h1 : (((frobeniusEquiv (Per.Fl l) l).symm^[n]) x).untilt = 0 := by
    have h := rootT_pow x n
    rw [hx] at h
    exact pow_eq_zero_iff (pow_ne_zero n (Fact.out : l.Prime).ne_zero) |>.1 h
  have h2 := PreTilt.mk_untilt_eq_coeff_zero (((frobeniusEquiv (Per.Fl l) l).symm^[n]) x)
  rw [h1, map_zero] at h2
  have h3 := PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n x
  rw [zero_add] at h3
  have hc : PreTilt.coeff n x = PreTilt.coeff n 0 := by rw [map_zero, ← h3, ← h2]
  simpa only [PreTilt.coeff_def] using hc

theorem untilt_ultrametric_definite (l : ℕ) [Fact l.Prime] (x y : Per.Fl l) :
    ‖(((x + y).untilt : Per.OC l) : ℂ_[l])‖ ≤
      max ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ‖((y.untilt : Per.OC l) : ℂ_[l])‖ ∧
    (x.untilt = 0 → x = 0) := by
  refine ⟨?_, eq_zero_of_untilt x⟩
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have ht : Filter.Tendsto (fun n : ℕ => ‖((l : ℕ) : ℂ_[l])‖ ^ l ^ n) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_l_lt).comp
      (tendsto_pow_atTop_atTop_of_one_lt hl)
  have h2 := (tendsto_const_nhds (x := max ‖((x.untilt : Per.OC l) : ℂ_[l])‖
    ‖((y.untilt : Per.OC l) : ℂ_[l])‖)).max ht
  have h3 := ge_of_tendsto' h2 (bound x y)
  rwa [max_eq_left (le_max_of_le_left (norm_nonneg _))] at h3

end GlobalTheory.TiltAbs
end
end
