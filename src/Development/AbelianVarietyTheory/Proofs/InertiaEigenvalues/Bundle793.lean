module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle783
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle735
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle736
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle706
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle784
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle024
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKExp

theorem muPow_smul_crisVal_integral : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O) (b₀ : TW (OB l O) T), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ → ∀ ε : OCb l, IsEps ε → ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η)) • b₀ = TWincl (toB l O) T z := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hyY hy m₀ b₀ hm hb ε hε
  obtain ⟨δ, hδ, -⟩ := hε.2
  have hEM : y ∈ D.toPhiMod.EM η := hyY.1
  obtain ⟨-, hLA⟩ := GlobalTheory.T.breuilKisin_mu_pow_smul_frobenius_mem_ainf l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ ⟨y, hy⟩ hEM m₀ hm
  obtain ⟨c, hc⟩ := hLA
  have hU := ((GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ).2.2.2.1
  obtain ⟨z, hz⟩ := ((GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ).2.2.2) _ ⟨c, rfl⟩
  have hC := ((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι D.toPhiMod T R.I).2 R.jB R.cmp).2.1
  have e1 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) = (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (muOf ε)) := rfl
  have hpow : ∀ n : ℕ, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n)) = (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε)) ^ n := by
    intro n
    rw [← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]
  have hunit : ∀ n : ℕ, IsUnit (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n))) := by
    intro n
    rw [hpow, e1]
    exact (hU.map (Algebra.TensorProduct.includeRight (R := ℤ_[l]) (A := O))).pow n
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ (H + η)) with hmdef
  obtain ⟨u, hu⟩ := hunit (H + η)
  have hval : IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀)
      ((↑u⁻¹ : OB l O) • R.jB (fun i => toB l O (c i))) := by
    refine ⟨m, c, ⟨u, hu⟩, hc.symm, ?_⟩
    rw [← hu, smul_smul, Units.mul_inv, one_smul]
  have hb0 := hC _ _ _ hb hval
  have hmain : toB l O m • b₀ = R.jB (fun i => toB l O (c i)) := by
    rw [hb0, ← hu, smul_smul, Units.mul_inv, one_smul]
  set c' : ι → OA l O := fun i => ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * c i with hc'
  have hL : inclO l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) • inclL t ϖ D.toPhiMod c = inclL t ϖ D.toPhiMod c' := by
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [hc', map_mul]
  rw [hL] at hz
  have hcmp := R.cmp c' z hz
  refine ⟨z, ?_⟩
  rw [← hcmp]
  have e2 : ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) ^ (H + 2 * η) = ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * m := by
    rw [hmdef, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← pow_add, Algebra.TensorProduct.tmul_pow, one_pow]
    ring_nf
  have e3 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η)) = toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * toB l O m := by
    first
    | rw [e2, map_mul]
    | rw [hmdef, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← pow_add]; ring_nf
  rw [e3, mul_smul, hmain, ← map_smul]
  congr 1
  funext i
  simp [hc', map_mul]

end GlobalTheory.BKExp
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.HorizXi

section General

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι : Type} [Fintype ι] [DecidableEq ι]


omit [NeZero a] [NeZero e] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedAlgebra ℚ_[l] K] in
theorem desc_succ_eq_zero {P : PhiMod O K l e a ι} (D : Conn P) {v : Vec K a ι} (hv : D.N v = 0) (i : ℕ) :
    D.desc (i + 1) v = 0 := by
  induction i with
  | zero => simp [Conn.desc_succ, Conn.desc_zero, hv]
  | succ i ih => rw [Conn.desc_succ, hv, zero_sub, map_neg, map_nsmul, ih, smul_zero, neg_zero]

theorem muDiv_zero (g : ↥(GK (ϖ.field a))) : ϖ.muDiv a O g 0 = 1 := by
  simp only [PiSys.muDiv, dpow_zero]
  rfl

theorem taylor_fix (g : ↥(GK (ϖ.field a))) {P : PhiMod O K l e a ι} (D : Conn P) (Γ : Matrix ι ι (OA l O))
    (m : P.MM) (hm : D.N m.1 = 0)
    (h : ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ z : ι → OCr l O,
      (Γ.map (toOCr l O) *ᵥ fun i => galOCr O g (toCris t ϖ P m i)) -
        ∑ i ∈ Finset.range n, ϖ.muDiv a O g i • toCris t ϖ P ⟨D.desc i m, D.desc_mem i m.2⟩ =
          (l : OCr l O) ^ r • z) :
    (Γ.map (toOCr l O) *ᵥ fun i => galOCr O g (toCris t ϖ P m i)) = toCris t ϖ P m := by
  have hsum : ∀ n, ∑ i ∈ Finset.range (n + 1),
      ϖ.muDiv a O g i • toCris t ϖ P ⟨D.desc i m, D.desc_mem i m.2⟩ = toCris t ϖ P m := by
    intro n
    rw [Finset.sum_range_succ']
    have h0 : ∀ i ∈ Finset.range n, ϖ.muDiv a O g (i + 1) •
        toCris t ϖ P ⟨D.desc (i + 1) m, D.desc_mem (i + 1) m.2⟩ = 0 := by
      intro i _
      have : (⟨D.desc (i + 1) m, D.desc_mem (i + 1) m.2⟩ : P.MM) = 0 :=
        Subtype.ext (desc_succ_eq_zero D hm i)
      rw [this, map_zero, smul_zero]
    rw [Finset.sum_eq_zero h0, zero_add, muDiv_zero, one_smul]
    exact congrArg _ (Subtype.ext (D.desc_zero m))
  funext i
  rw [← sub_eq_zero]
  refine sep_OCr _ fun r => ?_
  obtain ⟨n₀, hn₀⟩ := h r
  obtain ⟨z, hz⟩ := hn₀ (n₀ + 1) (Nat.le_succ _)
  rw [hsum] at hz
  exact ⟨z i, by rw [← Pi.sub_apply, hz, Pi.smul_apply, smul_eq_mul]⟩

theorem toBcris_eq_toOB {P : PhiMod O K l e a ι} (m : P.MMl) (hm : m.1 ∈ P.MM) (i : ι) :
    toBcris t ϖ P m i = toOB l O (toCris t ϖ P ⟨m.1, hm⟩ i) := by
  rw [toBcris_apply, toCris_apply, ← ϖ.iB_of_mem t K]
  rfl

theorem exists_pow_smul_mem_MM {P : PhiMod O K l e a ι} (m : P.MMl) :
    ∃ N : ℕ, (((l ^ N : ℕ) • m : P.MMl) : Vec K a ι) ∈ P.MM := by
  have hc : ∀ τ i, ∃ n : ℕ, ((l : S O K e) : K⟦X⟧) ^ n * (P.mxInv τ *ᵥ m.1 τ) i ∈ S O K e :=
    fun τ i => mem_away.1 (P.mem_extc_iff.1 (mem_tot.1 m.2 τ) i)
  choose n hn using hc
  refine ⟨∑ τ, ∑ i, n τ i, mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => ?_⟩
  have hle : n τ i ≤ ∑ τ, ∑ i, n τ i :=
    (Finset.single_le_sum (f := fun i => n τ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun τ => ∑ i, n τ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ))
  have h1 : ((((l ^ (∑ τ, ∑ i, n τ i) : ℕ) • m : P.MMl) : Vec K a ι)) τ =
      ((l : S O K e) : K⟦X⟧) ^ (∑ τ, ∑ i, n τ i) • m.1 τ := by
    rw [Submodule.coe_smul_of_tower, Pi.smul_apply, ← Nat.cast_smul_eq_nsmul K⟦X⟧]
    simp
  rw [h1, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact (S O K e).mul_mem ((S O K e).pow_mem (SetLike.coe_mem _) _) (hn τ i)

theorem actB_smul {G : Type} [Group G] [TopologicalSpace G] (s : G →* GQ l) (T : LocLat G ℚ_[l] K O) (g : G)
    (r : OB l O) (z : TW (OB l O) T) : actB s T g (r • z) = galOB O (s g) r • actB s T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w x =>
    simp only [actB, TWact, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

variable [TameDescentExponentData K l e a]

theorem actB_jB {P : PhiMod O K l e a ι} {T : LocLat (Gl l) ℚ_[l] K O} (I : Ident t ϖ P T)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (hjB : IsCrisCmp I jB) (g : Gl l)
    (Γ : Matrix ι ι (OA l O)) (hΓ : I.IsLMat (sQ l g) g Γ) (y : ι → OB l O) :
    actB (sQ l) T g (jB y) = jB (Γ.map (toB l O) *ᵥ fun i => galOB O (sQ l g) (y i)) := by
  obtain ⟨-, hI⟩ := GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι P T I
  obtain ⟨-, huniq, -, -, hgal⟩ := hI jB hjB
  have hstab := (I.exists_isLMat_iff (sQ l g) g).1 ⟨Γ, hΓ⟩
  have hval : ∀ c : ι → OA l O, IsCrisVal t ϖ P jB (inclL t ϖ P c) (jB fun i => toB l O (c i)) :=
    fun c => ⟨1, c, by simp, by simp, by simp⟩
  have hbas : ∀ j, actB (sQ l) T g (jB (Pi.single j 1)) = jB (Γ.map (toB l O) *ᵥ Pi.single j 1) := by
    intro j
    have e1 : (Pi.single j 1 : ι → OB l O) = fun i => toB l O ((Pi.single j 1 : ι → OA l O) i) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    have e2 : (Γ.map (toB l O) *ᵥ Pi.single j 1) = fun i => toB l O
        ((Γ *ᵥ fun k => galOA O (sQ l g) ((Pi.single j 1 : ι → OA l O) k)) i) := by
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite (galOA O (sQ l g)), apply_ite (toB l O)]
    have h1 := hgal g hstab _ _ (hval (Pi.single j 1))
    rw [hΓ] at h1
    rw [e2, e1]
    exact huniq _ _ _ h1 (hval _)
  conv_lhs => rw [pi_eq_sum_univ' y]

  rw [map_sum, map_sum]
  conv_rhs => rw [pi_eq_sum_univ' (fun i => galOB O (sQ l g) (y i))]

  rw [← Matrix.mulVecLin_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearEquiv.map_smul, actB_smul, hbas, map_smul, Matrix.mulVecLin_apply, LinearEquiv.map_smul]

theorem horiz_of_fix {P : PhiMod O K l e a ι} {T : LocLat (Gl l) ℚ_[l] K O} (I : Ident t ϖ P T)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (hjB : IsCrisCmp I jB) (g : Gl l)
    (Γ : Matrix ι ι (OA l O)) (hΓ : I.IsLMat (sQ l g) g Γ) (ξ : P.MMl) (N : ℕ)
    (hN : (((l ^ N : ℕ) • ξ : P.MMl) : Vec K a ι) ∈ P.MM)
    (hfix : (Γ.map (toOCr l O) *ᵥ fun i => galOCr O (sQ l g) (toCris t ϖ P ⟨_, hN⟩ i)) =
      toCris t ϖ P ⟨_, hN⟩) :
    actB (sQ l) T g (jB (toBcris t ϖ P ξ)) = jB (toBcris t ϖ P ξ) := by
  have hB : (Γ.map (toB l O) *ᵥ fun i => galOB O (sQ l g) (toBcris t ϖ P ((l ^ N : ℕ) • ξ) i)) =
      toBcris t ϖ P ((l ^ N : ℕ) • ξ) := by
    funext i
    rw [toBcris_eq_toOB t ϖ _ hN i, ← hfix]

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, toBcris_eq_toOB t ϖ _ hN, galOB_toOB,
    Matrix.map_apply, toB, AlgHom.comp_apply]
  rw [map_nsmul] at hB
  have hu : IsUnit ((l ^ N : ℕ) : OB l O) := by
    rw [Nat.cast_pow]; exact isUnit_l_OB.pow N
  have hg : (fun i => galOB O (sQ l g) (((l ^ N : ℕ) • toBcris t ϖ P ξ) i)) =
      (l ^ N : ℕ) • fun i => galOB O (sQ l g) (toBcris t ϖ P ξ i) := by
    funext i
    simp only [Pi.smul_apply, map_nsmul]
  rw [hg, Matrix.mulVec_smul] at hB
  have hfx : (Γ.map (toB l O) *ᵥ fun i => galOB O (sQ l g) (toBcris t ϖ P ξ i)) = toBcris t ϖ P ξ := by
    funext i
    have h3 := congrFun hB i
    simp only [Pi.smul_apply, ← Nat.cast_smul_eq_nsmul (OB l O), smul_eq_mul] at h3
    exact hu.mul_left_cancel h3
  rw [actB_jB t ϖ I jB hjB g Γ hΓ _, hfx]

end General

end GlobalTheory.HorizXi

namespace GlobalTheory.HorizXi

theorem galois_fixes_xi : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T), IsCrisCmp I jB → ∀ C : Conn P, C.nabla = P.nabla → Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C → IsHoriz (thetaW a LL) ϖ (sQ l) P jB := by
  intro l _ a e _ _ ϖ LL _ _ _ ι _ _ P T I jB hjB C hC hTay g hg d hξ
  have h1 := hTay ⟨sQ l g, hg⟩
  obtain ⟨Γ, h2⟩ := h1
  have h3 := exists_pow_smul_mem_MM (⟨P.xi d, hξ⟩ : P.MMl)
  obtain ⟨N, hN⟩ := h3
  have hNm : C.N (((l ^ N : ℕ) • (⟨P.xi d, hξ⟩ : P.MMl) : P.MMl) : Vec _ a ι) = 0 := by
    rw [Submodule.coe_smul_of_tower, map_nsmul, Conn.N_apply, hC, PhiMod.nabla_xi, smul_zero, smul_zero]
  exact horiz_of_fix (thetaW a LL) ϖ I jB hjB g Γ h2.1 _ N hN
    (taylor_fix (thetaW a LL) ϖ ⟨sQ l g, hg⟩ C Γ ⟨_, hN⟩ hNm (h2.2 ⟨_, hN⟩))

end GlobalTheory.HorizXi
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.Natural

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem inclL_smul (P : PhiMod O K l e a ι) (r : OA l O) (c : ι → OA l O) :
    inclL t ϖ P (r • c) = inclO l O r • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [map_mul]

theorem homW_inclL {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q) (c : ι → OA l O) :
    homW t ϖ F (inclL t ϖ P c) = inclL t ϖ Q (((homMat t ϖ F).map (frobOA l O)) *ᵥ c) := by
  rw [homW_apply, inclL_apply, Matrix.mulVec_mulVec, homMat_mul_frobMat, ← Matrix.mulVec_mulVec, inclL_apply]
  have hM : ((homMat t ϖ F).map (inclO l O)).map (frobOW l O) =
      ((homMat t ϖ F).map (frobOA l O)).map (inclO l O) := by
    ext i j; simp [frobOW_inclO]
  rw [hM]
  congr 1
  funext i
  exact (RingHom.map_mulVec (inclO l O).toRingHom _ _ i).symm


omit [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem map_id_smul {G : Type} [Group G] [TopologicalSpace G] {T T' : LocLat G ℚ_[l] K O}
    (g : ↥T.L.T →ₗ[O] ↥T'.L.T) (r : OB l O) (x : TW (OB l O) T) :
    TensorProduct.map LinearMap.id g (r • x) = r • TensorProduct.map LinearMap.id g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b y => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem toBcris_hom {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q) (m : P.MMl)
    (m' : Q.MMl) (hm : m'.1 = F.app m.1) :
    toBcris t ϖ Q m' = (((homMat t ϖ F).map (frobOA l O)).map (toB l O)) *ᵥ toBcris t ϖ P m := by
  have hmat : ∀ τ, Q.mxInv τ * F.mat τ = (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := fun τ => by
    calc Q.mxInv τ * F.mat τ = Q.mxInv τ * F.mat τ * (P.mx τ * P.mxInv τ) := by
          rw [P.mx_mul_mxInv, Matrix.mul_one]
      _ = Q.mxInv τ * (F.mat τ * P.mx τ) * P.mxInv τ := by simp only [Matrix.mul_assoc]
      _ = Q.mxInv τ * Q.mx τ * (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := by
          rw [F.comm]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Q.mxInv_mul_mx, Matrix.one_mul]
  have hA : ∀ (g : ZMod a → A O K) (h : ∀ τ, (g τ : K⟦X⟧) ∈ invL l (S O K e)),
      ϖ.iB t K (fun τ => ⟨(g τ : K⟦X⟧), h τ⟩) = toB l O (ϖ.iTot t K g) := fun g h =>
    (ϖ.iB_of_mem t K (fun τ => ⟨g τ, A_le_S l e (g τ).2⟩)).trans
      (congrArg (toOB l O) (ϖ.iC_of_mem t K g))
  funext i
  rw [toBcris_apply, Matrix.mulVec, dotProduct]
  simp only [Matrix.map_apply, toBcris_apply, homMat, Matrix.of_apply, ← PiSys.iTot_frob]
  trans ∑ j, ϖ.iB t K (fun τ => ⟨(frobAc l (fun τ => ⟨F.mat τ i j, F.mem τ i j⟩) τ : K⟦X⟧),
      le_away _ _ (A_le_S l e (Subtype.prop _))⟩) * ϖ.iB t K (_root_.GlobalTheory.BKReal.coordL P (invL l (S O K e)) m j)
  swap
  · exact Finset.sum_congr rfl fun j _ => by rw [hA]

  simp only [← map_mul, ← map_sum]
  congr 1
  funext τ
  apply Subtype.ext
  have h1 := congrFun (congrArg (· *ᵥ (m.1 τ)) (hmat τ)) i
  simp only [← Matrix.mulVec_mulVec] at h1
  simp only [Finset.sum_apply, Pi.mul_apply, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
  change (Q.mxInv τ *ᵥ m'.1 τ) i = ∑ j, frob K l (F.mat (τ - 1) i j) * (P.mxInv τ *ᵥ m.1 τ) j
  rw [hm, BK.Hom.app_apply, h1]
  rfl

variable [TameDescentExponentData K l e a]

theorem jB_hom {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat (Gl l) ℚ_[l] K O}
    {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T}
    {jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T'} (hB : IsCrisCmp I jB) (hB' : IsCrisCmp I' jB')
    {f : LatHom T.L T'.L} {F : BK.Hom P Q} (hF : IsMapOf I I' f F) (v : ι → OB l O) :
    jB' ((((homMat t ϖ F).map (frobOA l O)).map (toB l O)) *ᵥ v) =
      TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (jB v) := by
  set Φ := TensorProduct.map (LinearMap.id : OB l O →ₗ[O] OB l O) ((f.f.restrictScalars O).restrict f.T_le) with hΦ
  set H := (homMat t ϖ F).map (frobOA l O) with hH
  let Pr : (ι → OB l O) → Prop := fun v => jB' (H.map (toB l O) *ᵥ v) = Φ (jB v)
  have hsm : ∀ (r : OB l O) v, Pr (r • v) ↔ r • jB' (H.map (toB l O) *ᵥ v) = r • Φ (jB v) := by
    intro r v
    change jB' (H.map (toB l O) *ᵥ (r • v)) = Φ (jB (r • v)) ↔ _
    rw [Matrix.mulVec_smul, map_smul, map_smul, hΦ, map_id_smul]
  have hcancel : ∀ (r : OB l O) v, IsUnit r → Pr (r • v) → Pr v := fun r v hr h =>
    (hr.smul_left_cancel).1 ((hsm r v).1 h)
  have hofT : ∀ x : ↥T.L.T, Pr (jB.symm ((1 : OB l O) ⊗ₜ[O] x)) := by
    intro x
    obtain ⟨m, c, hu, hc, hb⟩ := ((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι P T I).2 jB hB).2.2.2.1 x
    obtain ⟨m', c', hu', hc', hb'⟩ :=
      ((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ κ Q T' I').2 jB' hB').2.2.2.1 ⟨f.f x, f.T_le _ x.2⟩
    refine hcancel (toB l O m) _ hu ?_
    have e1 : toB l O m • jB.symm ((1 : OB l O) ⊗ₜ[O] x) = fun i => toB l O (c i) := by
      rw [← map_smul, hb, LinearEquiv.symm_apply_apply]
    change jB' (H.map (toB l O) *ᵥ _) = Φ (jB _)
    rw [e1]
    have e2 : (H.map (toB l O) *ᵥ fun i => toB l O (c i)) = fun i => toB l O ((H *ᵥ c) i) :=
      funext fun i => (RingHom.map_mulVec (toB l O).toRingHom _ _ i).symm
    have hc2 : inclO l O m • I'.ofT ⟨f.f x, f.T_le _ x.2⟩ = inclL t ϖ Q (H *ᵥ c) := by
      rw [← hF.homW_ofT x, ← (homW t ϖ F).map_smul, hc, homW_inclL]
    have heq : m' • (H *ᵥ c) = m • c' := by
      apply inclL_injective t ϖ Q
      rw [inclL_smul, inclL_smul, ← hc2, ← hc', smul_comm]
    have heqB : toB l O m' • (fun i => toB l O ((H *ᵥ c) i)) = toB l O m • fun i => toB l O (c' i) := by
      funext i
      have := congrArg (toB l O) (congrFun heq i)
      simpa [map_mul] using this
    have e3 : jB' (fun i => toB l O ((H *ᵥ c) i)) = toB l O m • ((1 : OB l O) ⊗ₜ[O] (⟨f.f x, f.T_le _ x.2⟩ : ↥T'.L.T)) := by
      refine (hu'.smul_left_cancel).1 ?_
      rw [← map_smul, heqB, map_smul, ← hb', smul_comm]
    rw [e2, e3, ← hb, hΦ, map_id_smul]
    rfl
  obtain ⟨y, rfl⟩ := jB.symm.surjective v
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    have : b ⊗ₜ[O] x = b • ((1 : OB l O) ⊗ₜ[O] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact (hsm b _).2 (by rw [hofT x])
  | add x y hx hy =>
    change jB' (H.map (toB l O) *ᵥ _) = Φ (jB _)
    rw [map_add (f := _), Matrix.mulVec_add, map_add (f := _), map_add (f := _), map_add (f := _)]
    exact congrArg₂ (· + ·) hx hy

theorem isCrisVal_hom {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat (Gl l) ℚ_[l] K O}
    {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T}
    {jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T'} (hB : IsCrisCmp I jB) (hB' : IsCrisCmp I' jB')
    {f : LatHom T.L T'.L} {F : BK.Hom P Q} (hF : IsMapOf I I' f F) {w : ι → OW l O} {b : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) :
    IsCrisVal t ϖ Q jB' (homW t ϖ F w)
      (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) b) := by
  obtain ⟨m, c, hu, hc, hb⟩ := h
  refine ⟨m, ((homMat t ϖ F).map (frobOA l O)) *ᵥ c, hu, ?_, ?_⟩
  · rw [← (homW t ϖ F).map_smul, hc, homW_inclL]
  · rw [← map_id_smul ((f.f.restrictScalars O).restrict f.T_le), hb, ← jB_hom t ϖ hB hB' hF]
    congr 1
    funext i
    exact (RingHom.map_mulVec (toB l O).toRingHom _ _ i).symm

end GlobalTheory.BKGal.Natural

theorem GlobalTheory.BKGal.cris_natural : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Q : PhiMod O K l e a κ) (T' : LocLat (Gl l) ℚ_[l] K O) (I' : Ident t ϖ Q T') (jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T') (f : LatHom T.L T'.L) (F : GlobalTheory.BK.Hom P Q), IsCrisCmp I' jB' → IsMapOf I I' f F → (∀ (m : P.MMl) (m' : Q.MMl), m'.1 = F.app m.1 → jB' (toBcris t ϖ Q m') = TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (jB (toBcris t ϖ P m))) ∧ ∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ Q jB' (homW t ϖ F w) (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) b) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I jB hB κ _ _ Q T' I' jB' f F hB' hF
  refine ⟨fun m m' hm => ?_, fun w b hw => GlobalTheory.BKGal.Natural.isCrisVal_hom t ϖ hB hB' hF hw⟩
  rw [GlobalTheory.BKGal.Natural.toBcris_hom t ϖ F m m' hm]
  exact GlobalTheory.BKGal.Natural.jB_hom t ϖ hB hB' hF _
end
end

section

open Matrix GlobalTheory.SplitHecke GlobalTheory.ExportSeries

theorem _root_.GlobalTheory.T.sum_hecke_indicator_integral_eq_primitive : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Finite (IsLocalRing.ResidueField O)] (p : O), Irreducible p → ∀ (r n : ℕ) (ι : Type) (α : ℕ → GL (Fin r) K) (R : ℕ → Finset ι) (ρ : ι → GL (Fin r) K), (∀ k ∈ Finset.Icc 1 r, Hk O p k (α k) ∧ Reps O (α k) (R k) ρ) → ∀ z : Matrix (Fin r) (Fin n) O, (1 : ℂ) + ∑ k ∈ Finset.Icc 1 r, (-1 : ℂ) ^ k * (Nat.card (IsLocalRing.ResidueField O) : ℂ) ^ (k * (k - 1) / 2) * (Nat.card {γ : ι // γ ∈ R k ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))} : ℂ) = ((prim (z.map (IsLocalRing.residue O)) : ℚ) : ℂ) := by
  first | exact @GlobalTheory.HeckeMobius.sum_hecke_indicator_eq_prim | exact GlobalTheory.HeckeMobius.sum_hecke_indicator_eq_prim | (intros; apply GlobalTheory.HeckeMobius.sum_hecke_indicator_eq_prim <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.TypeRec.TwistInert

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

section Val

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem valuation_lt_one_iff_tendsto (x : K) :
    valuation K x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  refine ⟨GlobalTheory.LocalTraceSum.tendsto_pow, fun h => ?_⟩
  have hO := GlobalTheory.LocalTraceSum.isOpen_lt (K := K) 1
  obtain ⟨n, hn⟩ := (h.eventually (hO.mem_nhds (by simp))).exists
  by_contra hx
  have h1 : 1 ≤ valuation K x := not_lt.1 hx
  have h2 : 1 ≤ valuation K (x ^ n) := by rw [map_pow]; exact one_le_pow₀ h1
  exact absurd hn (not_lt.2 h2)

theorem valuation_lt_one_map (f : K →+* L) (hf : Continuous f) {x : K} (hx : valuation K x < 1) :
    valuation L (f x) < 1 := by
  rw [valuation_lt_one_iff_tendsto] at hx ⊢
  simpa [Function.comp_def, map_pow] using (hf.tendsto 0).comp hx

end Val

def twistEquiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) (χ : G →* ℂˣ) :
    (_root_.GlobalTheory.SmGL.twist π χ).Equiv (_root_.GlobalTheory.SmGL.twist σ χ) :=
  Representation.Equiv.mk φ.toLinearEquiv fun g => LinearMap.ext fun x => by
    have e := LinearMap.congr_fun (φ.isIntertwining' g) x
    simp only [LinearMap.comp_apply] at e
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, twist_apply, map_smul]
    congr 1

end GlobalTheory.TypeRec.TwistInert
end
end
