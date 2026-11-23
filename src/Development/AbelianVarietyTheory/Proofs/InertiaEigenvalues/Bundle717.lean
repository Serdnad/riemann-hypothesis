module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle574
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle705
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle706
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle700
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle229
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle264
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNoetherianRingOL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle421
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinesAtOfLatticeAtLevels
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle078
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle701
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle702
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem ringHom_ext_of_sep_galPer {R B : Type} [CommRing R] [CommRing B] {f g : R⟦X⟧ →+* B}
    (hC : ∀ r, f (C r) = g (C r)) (hX : f X = g X) (hsep : ∀ b : B, (∀ n, f X ^ n ∣ b) → b = 0) :
    f = g := by
  have hp : ∀ p : Polynomial R, f p = g p := fun p => by
    induction p using Polynomial.induction_on with
    | C a => simpa using hC a
    | add p q hp hq => simp [hp, hq]
    | monomial n a _ => simp [hC, hX]
  ext1 a
  rw [← sub_eq_zero]
  refine hsep _ fun n => ?_
  rw [a.eq_X_pow_mul_shift_add_trunc n, map_add (f := _), map_add (f := _), hp, map_mul, map_mul, map_pow, map_pow, ← hX]
  exact ⟨_, by rw [add_sub_add_right_eq_sub, ← mul_sub]⟩

theorem mat_mul_right_cancel_galPer {R : Type} [CommRing R] [IsDomain R] {n : Type} [Fintype n] [DecidableEq n]
    {A B P : Matrix n n R} (hP : P.det ≠ 0) (h : A * P = B * P) : A = B := by
  have h2 : (A - B) * P = 0 := by rw [Matrix.sub_mul, h, sub_self]
  have h3 : P.det • (A - B) = 0 := by
    rw [← Matrix.mul_one (A - B), ← Matrix.mul_smul, ← Matrix.mul_adjugate P, ← Matrix.mul_assoc, h2,
      Matrix.zero_mul]
  rw [← sub_eq_zero]
  ext i j
  have h4 := congr_fun₂ h3 i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h4
  rw [Matrix.zero_apply]
  exact (mul_eq_zero.1 h4).resolve_left hP

theorem mat_smul_cancel_galPer {R : Type} [CommRing R] [IsDomain R] {m n : Type} {c : R} (hc : c ≠ 0)
    {A B : Matrix m n R} (h : c • A = c • B) : A = B := by
  ext i j
  have h1 := congr_fun₂ h i j
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at h1
  exact mul_left_cancel₀ hc h1

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

namespace BK

variable (bk : BK K)

theorem X_pow_mem_J_galPer : (X : bk.S) ^ bk.Ep.natDegree ∈ bk.J := by
  apply GlobalTheory.BSP.BK.X_pow_natDegree_mem_lE <;> assumption

theorem ev_sep_galPer (b : Ainf l) (hb : ∀ n, bk.ev X ^ n ∣ b) : b = 0 := by
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hc := tb.complete
  refine IsHausdorff.haus hc.toIsHausdorff b fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  obtain ⟨c, hc⟩ := hb (bk.Ep.natDegree * n)
  rw [hc, pow_mul, ← map_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_map_of_mem bk.ev bk.X_pow_mem_J_galPer) n)

theorem σA_ev_galPer {g : ↥(GK K)} (hg : bk.FixFlat g) (a : bk.S) : Per.σA (g : GQ l) (bk.ev a) = bk.ev a := by
  have hg' : Per.σF (g : GQ l) bk.flat = bk.flat := hg
  have hX : ((Per.σA (g : GQ l)).comp bk.ev) X = bk.ev X := by
    show Per.σA _ (bk.ev X) = bk.ev X
    rw [bk.ev_X, GlobalTheory.RingIface.sigA_teich, hg']
  have h := ringHom_ext_of_sep_galPer (f := (Per.σA (g : GQ l)).comp bk.ev) (g := bk.ev)
    (fun w => by
      show Per.σA _ (bk.ev (C w)) = bk.ev (C w)
      rw [bk.ev_C, bk.gal_w]) hX
    (fun b hb => bk.ev_sep_galPer b fun n => by rw [← hX]; exact hb n)
  exact RingHom.congr_fun h a

theorem ev_injective_galPer : Function.Injective bk.ev := by
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have key : ∀ a, tb.c tb.i₀ (bk.ev a * tb.b tb.i₀) = a := fun a => by
    rw [tb.c_mul, tb.c_self, mul_one]
  intro a a' h
  rw [← key a, ← key a', h]

theorem ρ₀_pos_lt_one_galPer : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos (one_div_pos.2 he))

end BK

theorem seed_gal_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ),
    ∀ g : ↥(GK K), bk.FixFlat g → ∀ G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G →
      (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → ∀ x, G (j x) = j x) ∧
      bk.iA τ ^ s.N • ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G) =
        G (bk.iA τ) ^ s.N • s.W := by
  intro l _ K bk τ _ d ρ _ s g hg G hG
  obtain ⟨h0, h1⟩ := bk.ρ₀_pos_lt_one_galPer
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  have hGS : ∀ a, G (bk.iA (bk.ev a)) = bk.iA (bk.ev a) := fun a => by
    show G (toDisc l (bk.ev X) bk.ρ₀ (bk.ev a)) = _
    rw [hG.ext, bk.σA_ev_galPer hg]
  have hGτ : G (bk.iA τ) = bk.iA (Per.σA (g : GQ l) τ) := hG.ext τ
  refine ⟨fun j hj x => ?_, ?_⟩
  · have hGj : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev (G.comp j) :=
      ⟨fun a => by
        show G (j (toDisc l X bk.ρ₀ a)) = _
        rw [hj.ext]; exact hGS a,
       fun x => (hG.norm_le _).trans (hj.norm_le x)⟩
    exact RingHom.congr_fun (IsDiscMap.unique hGj hj) x
  · have he : bk.iA (bk.ev bk.E) ≠ 0 := fun h =>
      bk.E_ne_zero (bk.ev_injective_galPer (hinj (h.trans (map_zero _).symm) |>.trans (map_zero _).symm))
    have hl0 : ((l : ℕ) : bk.DA bk.ρ₀) ≠ 0 := (isUnit_l_disc l (bk.ev X) bk.ρ₀).ne_zero
    have hdet : (s.X'.map bk.iS).det ≠ 0 := by
      intro h0'
      have hm := congrArg (fun M => (M.map bk.iS).det) s.X_mul
      rw [Matrix.map_mul, Matrix.det_mul, h0', mul_zero] at hm
      have hc : (((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) bk.S)).map bk.iS =
          bk.iS ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [hc, Matrix.det_smul, Matrix.det_one, mul_one] at hm
      have h3 := pow_eq_zero_iff'.1 hm.symm
      rw [map_mul, map_pow, map_pow, map_natCast] at h3
      exact mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ he) h3.1
    have hX' : (s.X'.map bk.iS).map G = s.X'.map bk.iS := by
      rw [Matrix.map_map]
      congr 1
      funext a
      exact hGS a
    have hσ : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) = bk.iA (bk.ev bk.E) * G (bk.iA τ) := by
      rw [map_mul, bk.σA_ev_galPer hg, map_mul, hGτ]
    have h := s.gal g G hG
    rw [Matrix.map_mul, hX', hσ, map_mul, mul_pow, mul_pow, mul_smul, mul_smul] at h
    have h' := mat_smul_cancel_galPer (pow_ne_zero _ he) h
    refine mat_mul_right_cancel_galPer hdet ?_
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc]
    exact h'

end GlobalTheory.BSP
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.semistable_cocycle_of_frobenius_monodromy_pair : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ x ∈ Dst P ρ, ∀ y ∈ Dst P ρ, (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), c ∈ continuousCocycles ρ ∧ (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ monV P ℚ_[l] V z = x := by
  first | exact @GlobalTheory.semistable_class_of_pair | exact GlobalTheory.semistable_class_of_pair | (intros; apply GlobalTheory.semistable_class_of_pair <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.teichmullerTiltMinusOne_associated : ∀ (l : ℕ) [Fact l.Prime] (e e' : OCb l), IsEps e → IsEps e' → Associated (mu e) (mu e') := by
  first | exact @GlobalTheory.EpsilonAssociated.mu_associated | exact GlobalTheory.EpsilonAssociated.mu_associated | (intros; apply GlobalTheory.EpsilonAssociated.mu_associated <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_primitiveRoot_in_rayClassField_natModulus : ∀ {K H : Type} [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) → ∃ ζ : H, IsPrimitiveRoot ζ n := by
  first | exact @GlobalTheory.RayRootOfUnity.exists_isPrimitiveRoot_of_isRay | exact GlobalTheory.RayRootOfUnity.exists_isPrimitiveRoot_of_isRay | (intros; apply GlobalTheory.RayRootOfUnity.exists_isPrimitiveRoot_of_isRay <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.isGalois_rat_complexImage_rayClassField : ∀ {K H : Type} [Field K] [NumberField K] [IsGalois ℚ K] [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) → ∀ j : H →+* ℂ, IsGalois ℚ j.toRatAlgHom.fieldRange := by
  first | exact @GlobalTheory.RayNatGalois.isGalois_fieldRange | exact GlobalTheory.RayNatGalois.isGalois_fieldRange | (intros; apply GlobalTheory.RayNatGalois.isGalois_fieldRange <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem norm_sub_lt_one_of_mem_inertia {l : ℕ} [Fact l.Prime] (K : FinExt l) (σ : ↥(GK K)) (hσ : σ ∈ IK K) :
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖(σ : GQ l) x - x‖ < 1 := by
  unfold IK at hσ
  induction hσ using Subgroup.closure_induction with
  | mem σ h => exact h
  | one => intro x _; simp
  | mul σ τ _ _ hσ hτ =>
    intro x hx
    have h1 : ‖(τ : GQ l) x‖ ≤ 1 := by rw [GlobalTheory.RingBasics.norm_gal]; exact hx
    have e : ((σ * τ : ↥(GK K)) : GQ l) x - x
        = ((σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x) + ((τ : GQ l) x - x) := by
      rw [Subgroup.coe_mul, AlgEquiv.mul_apply]; ring
    rw [e]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hσ _ h1) (hτ _ hx))
  | inv σ _ hσ =>
    intro x hx
    have h1 : ‖((σ : GQ l)⁻¹) x‖ ≤ 1 := by rw [GlobalTheory.RingBasics.norm_gal]; exact hx
    have h2 := hσ _ h1
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, norm_sub_rev] at h2
    rw [Subgroup.coe_inv]
    exact h2

theorem noTower : NoTower := by
  classical
  intro l _ K N hanti hopen hpow hroot hchar
  have : FiniteDimensional ℚ_[l] (K : IntermediateField ℚ_[l] (Om l)) := K.2
  have hGK : IsOpen ((GK K : Subgroup (GQ l)) : Set (GQ l)) := IntermediateField.fixingSubgroup_isOpen _
  have hmem : ∀ k (σ : ↥(GK K)), (σ : GQ l) ∈ (N k).map (GK K).subtype ↔ σ ∈ N k := fun k σ =>
    Subgroup.mem_map_iff_mem (GK K).subtype_injective
  obtain ⟨k, hk⟩ := GlobalTheory.T.noDetectedSubgroupTowerRat_proof l (fun k => (N k).map (GK K).subtype)
    (fun i j hij => Subgroup.map_mono (hanti hij))
    (fun k => hGK.isOpenMap_subtype_val _ (hopen k))
    (by
      rintro k _ ⟨σ, hσ, rfl⟩
      exact ⟨σ ^ l, hpow k σ hσ, rfl⟩)
    (by
      rintro j _ ⟨σ, hσ, rfl⟩ h
      exact ⟨σ, hroot j σ hσ ((hmem _ (σ ^ l)).1 h), rfl⟩)
    (by
      intro r
      obtain ⟨k₀, hk₀⟩ := hchar r
      refine ⟨k₀, fun k hk => ?_⟩
      obtain ⟨ι, hι, x, a, h1, h2⟩ := hk₀ k hk
      have key := fun i => GlobalTheory.T.approx_complexPadic_coboundary_algebraic_integer l r ((N k).map (GK K).subtype : Subgroup (GQ l)) (x i)
        (fun σ => if h : σ ∈ GK K then a i ⟨σ, h⟩ else 0) (by
          rintro _ ⟨σ, hσ, rfl⟩
          have := h1 i σ hσ
          simpa using this)
      choose y b hy hb using key
      refine ⟨ι, hι, y, b, fun i σ hσ => hy i σ hσ, ?_⟩
      rintro _ ⟨σ, hσ, rfl⟩ h
      refine ⟨σ, h2 σ hσ fun i => ?_, rfl⟩
      have := hb i _ (h i)
      simpa using this)
  refine ⟨k, fun j σ hσ => ?_⟩
  exact (hmem j σ).1 (hk j _ ((hmem k σ).2 hσ.2) (norm_sub_lt_one_of_mem_inertia K σ hσ.1))

end GlobalTheory.PMon.Ram
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

noncomputable section

namespace GlobalTheory.WachQN

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem invBasis_of_basisModule [Nontrivial O] (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {π' : LetA O n}
    (h : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π') :
    ∃ b : Fin (Module.finrank O ↥T.L.T) → W.DD T, (∀ j, b j ∈ W.NΔ T) ∧ LinearIndependent (LetA O n) b ∧
      W.N T = Submodule.span (LetA O n) (Set.range b) := by
  obtain ⟨⟨r, b, hbN, huniq, -⟩, -⟩ := h
  obtain ⟨a0, -, ha0⟩ := huniq 0 (W.N T).zero_mem
  have hli : LinearIndependent (LetA O n) b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    exact congrFun ((ha0 g hg.symm).trans (ha0 0 (by simp)).symm) j
  have hsp : W.N T = Submodule.span (LetA O n) (Set.range b) := by
    refine le_antisymm (fun x hx => ?_) (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact (hbN j).1))
    obtain ⟨a, ha, -⟩ := huniq x hx
    rw [ha]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hr : r = Module.finrank O ↥T.L.T := by
    let bN := (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hsp.symm)
    have hbc := W.N_base T hT
    let bD := (Algebra.TensorProduct.basis W.EE bN).map hbc.equiv
    haveI : Nontrivial W.EE := W.EE_inj.nontrivial
    rw [← (W.DD_free T).2, Module.finrank_eq_card_basis bD, Fintype.card_fin]
  subst hr
  exact ⟨b, hbN, hli, hsp⟩

end Generic

theorem invBasis_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), GlobalTheory.WachUse.InvBasis ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F h9 l _ K LL hA T hT
  have hbij : Function.Bijective (algebraMap ↥(K0 K) ↥K.1) :=
    ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩
  have hfr : Module.finrank ↥(K0 K) ↥K.1 = 1 :=
    (LinearEquiv.ofBijective (Algebra.linearMap ↥(K0 K) ↥K.1) hbij).finrank_eq.symm.trans (Module.finrank_self _)
  exact invBasis_of_basisModule _ T hT ((h9 l K 1 LL hA.2.2 T hT ((HW l).W_s K 1 LL hA.2.2)
    (by rw [(D.loc l).PD_p]; exact hA.2.1)).2.2 hfr).2

theorem heights_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), GlobalTheory.WachUse.Heights ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F h5 l _ K LL hA T U M hh hU hb i
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ).1
  have hJ := GlobalTheory.WachUse.HeightsProof.jumpsOverLetters_of_crysWith _ T U M hh hU hb
  have hp := h5 l K 1 LL hA.2.2 T M hh hU.1
    (fun τ j hτ => hJ j τ (fun c => by simpa using congrArg (fun f => f c) hτ))
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rw [← GlobalTheory.WachUse.HeightsProof.φD_letE]
    exact hp.1 i _ ⟨x, hx, rfl⟩
  · exact Submodule.span_mono (Set.image_mono (GlobalTheory.WachUse.HeightsProof.Nl_le _ T (i - 1)))
      (hp.2.1 i _ ⟨y, hy, rfl⟩)

theorem saturated_caseA (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) :
    GlobalTheory.WachUse.Saturated ((HW l).W K 1 LL hA.2.2) := by
  intro T' T f hT hb x hx
  have hT' : IsCrys ((D.loc l).PD K) T'.ρ :=
    GlobalTheory.HTW.Rec.isCrys_of_equiv ((D.loc l).PD K) (LinearEquiv.ofBijective f.f hb) f.equiv hT
  exact ((GlobalTheory.NL.Isog.isog_loc (HW l) K 1 LL hA.2.2 T' T f hT' hT hb).2.2 x).1 hx

theorem qN_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    tableLineDegreeTwo.admitted D HW F Cm → ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
      GlobalTheory.WachUse.QN ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F Cm h l _ K LL hA
  have hI := invBasis_of_admitted D HW F h.2.2.2.2.2.2.2.2.1 l K LL hA
  have hS := GlobalTheory.SenOperator.senOp_of_record D HW F Cm l K LL hA
  exact ⟨hI, heights_of_admitted D HW F h.2.2.2.2.1 l K LL hA,
    GlobalTheory.WachRankOne.rankOne_of_senOp (D.locA l) (HW l) (F l) (Cm l) K LL hA hI hS,
    saturated_caseA D HW l K LL hA,
    GlobalTheory.WachUse.additive_of_caseA (D.locA l) (HW l) (F l) (Cm l) K LL hA, hS⟩

end GlobalTheory.WachQN
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.cyclotomicTower_frobenius_formula_pos_weight : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ), 1 ≤ e → ∀ (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 → d - (l : ↥(K0 K)) ^ e * frK (LT l) K d = (frK (LT l) K ^ s) (∑ a ∈ primeTo l s, lam a) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) ((((1 + l ^ s : ℕ) : ℚ_[l]) ^ e - 1) / (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))) * cycVal (LT l) K s e lam d) := by
  first | exact @GlobalTheory.ExpImage.PosWeight.formula_pos | exact GlobalTheory.ExpImage.PosWeight.formula_pos | (intros; apply GlobalTheory.ExpImage.PosWeight.formula_pos <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.exists_finite_local_double_coset_representatives : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ α : GA D V, SuppF V f α → ∃ C : Finset (GA D V), (∀ γ ∈ C, SuppF V f γ) ∧ IsCosetRep V {k | k ∈ levG V β L ∧ SuppF V f k} α C := by
  first | exact @GlobalTheory.LocalRepsFin.exists_isCosetRep_finIdem | exact GlobalTheory.LocalRepsFin.exists_isCosetRep_finIdem | (intros; apply GlobalTheory.LocalRepsFin.exists_isCosetRep_finIdem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitaryFiniteAdeleIdentification_nonempty_presentations : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), Nonempty (FinIso L n) := by
  first | exact @GlobalTheory.FinIsoProof.finIso_nonempty | exact GlobalTheory.FinIsoProof.finIso_nonempty | (intros; apply GlobalTheory.FinIsoProof.finIso_nonempty <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.split_place_lattice_index_sum_le_zeta_sq_sub_one : ∀ (D : D7) (W : HSp D) (n : ℕ), 2 * W.rank + 5 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) → ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') → ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ (∏ i ∈ Finset.range W.rank, (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ ((i : ℝ) - (n : ℝ) / 2))⁻¹) ^ 2 - 1 := by
  first | exact @GlobalTheory.SplitIndexSum.indexSum_split | exact GlobalTheory.SplitIndexSum.indexSum_split | (intros; apply GlobalTheory.SplitIndexSum.indexSum_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.pairFixedVector_latticeVacuum_offLevels : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → GlobalTheory.FinZeta.VacFin R.ψ (Vc D i) (Wc D i) v (R.vP i t) := by
  first | exact @GlobalTheory.RawLift.vacFin_off | exact GlobalTheory.RawLift.vacFin_off | (intros; apply GlobalTheory.RawLift.vacFin_off <;> assumption)
end
