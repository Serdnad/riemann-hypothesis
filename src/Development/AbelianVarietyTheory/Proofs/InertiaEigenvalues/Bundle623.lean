module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle082
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle604
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle616
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle601
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.HodgeEx

theorem exists_hodge : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) → ∃ H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K, ∀ N : ℕ, (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) → ∀ i, |(H.p i : ℤ) - H.q| ≤ N := by
  intro l _ K P AI T C hC ξ hξ d ρ hDR
  set M : ↥(GK K) → Matrix (Fin d) (Fin d) P.R.BdR :=
    fun g => (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) with hM
  have hKact : ∀ (g : ↥(GK K)) (k : ↥K.1) (v : P.R.BdR),
      P.actQdR (g : GQ l) (algebraMap ↥K.1 P.R.BdR k * v) = algebraMap ↥K.1 P.R.BdR k * P.actQdR (g : GQ l) v := by
    intro g k v
    rw [← P.PD_actdR, ← P.PD_actdR, map_mul, AlgEquiv.commutes]
  let Iv : Submodule ↥K.1 (Fin d → P.R.BdR) :=
    { carrier := {c | ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c}
      add_mem' := by
        intro u v hu hv g
        simp only [Set.mem_setOf_eq] at hu hv ⊢
        have : (fun i => P.actQdR (g : GQ l) ((u + v) i)) =
            (fun i => P.actQdR (g : GQ l) (u i)) + (fun i => P.actQdR (g : GQ l) (v i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add, hu g, hv g]
      zero_mem' := by
        intro g
        simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero _
      smul_mem' := by
        intro k u hu g
        simp only [Set.mem_setOf_eq] at hu ⊢
        have : (fun i => P.actQdR (g : GQ l) ((k • u) i)) = k • (fun i => P.actQdR (g : GQ l) (u i)) := by
          funext i; simp only [Pi.smul_apply, Algebra.smul_def, hKact]
        rw [this, Matrix.mulVec_smul, hu g] }
  have hmemIv : ∀ c, c ∈ Iv ↔ ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c := fun c => Iff.rfl
  obtain ⟨x, hxli, hxinv, hxspan⟩ := GlobalTheory.T.exists_invariant_basis_of_isDeRham_lattice l P AI T K d ρ hDR
  set D : Submodule ↥K.1 (Fin d → P.R.BdR) := Submodule.span ↥K.1 (Set.range x) with hD
  have hDIv : D ≤ Iv := Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact (hmemIv _).2 (hxinv j))
  have hIvD : ∀ c, c ∈ Iv → c ∈ D := fun c hc => hxspan c hc
  haveI : FiniteDimensional ↥K.1 D := FiniteDimensional.span_of_finite ↥K.1 (Set.finite_range x)
  have hfr : Module.finrank ↥K.1 D = d := by
    rw [hD, finrank_span_eq_card hxli, Fintype.card_fin]
  let F : ℤ → Submodule ↥K.1 (Fin d → P.R.BdR) := fun a => Submodule.pi Set.univ (fun _ => (P.PD K).Fil a)
  have hmemF : ∀ a v, v ∈ F a ↔ ∀ i, v i ∈ (P.PD K).Fil a := fun a v => by
    simp [F, Submodule.mem_pi]
  have hFil : Antitone (P.PD K).Fil := antitone_int_of_succ_le (P.PD K).Fil_anti
  have hF : Antitone F := fun a b hab v hv => (hmemF _ _).2 fun i => hFil hab ((hmemF _ _).1 hv i)
  have hex : ∀ v ∈ D, ∃ a, v ∈ F a := by
    intro v _
    choose a ha using fun i => (P.PD K).Fil_exh (v i)
    refine ⟨-∑ i, |a i|, (hmemF _ _).2 fun i => hFil ?_ (ha i)⟩
    have h1 : |a i| ≤ ∑ j, |a j| := Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := neg_abs_le (a i)
    linarith
  have hsep : ∀ v ∈ D, (∀ a, v ∈ F a) → v = 0 := fun v _ hv =>
    funext fun i => (P.PD K).Fil_sep (v i) fun a => (hmemF a v).1 (hv a) i
  set_option synthInstance.maxHeartbeats 200000 in
  obtain ⟨b0, h0, hbF0, hbrep0⟩ := GlobalTheory.T.exists_filtration_adapted_basis_of_subspace D F hF hex hsep
  set e := finCongr hfr
  set b := b0.reindex e with hb
  set h : Fin d → ℤ := fun j => h0 (e.symm j) with hh
  have hbF : ∀ j, (b j : Fin d → P.R.BdR) ∈ F (h j) ∧ (b j : Fin d → P.R.BdR) ∉ F (h j + 1) := fun j => by
    rw [hb, Module.Basis.reindex_apply]; exact hbF0 _
  have hbrep : ∀ (a : ℤ) (v : D), (v : Fin d → P.R.BdR) ∈ F a → ∀ j, b.repr v j ≠ 0 → a ≤ h j := by
    intro a v hv j hj
    rw [hb, Module.Basis.repr_reindex_apply] at hj
    exact hbrep0 a v hv _ hj
  have hbinv : ∀ j (g : ↥(GK K)), M g *ᵥ (fun i => P.actQdR (g : GQ l) ((b j : Fin d → P.R.BdR) i)) = (b j : Fin d → P.R.BdR) :=
    fun j => (hmemIv _).1 (hDIv (b j).2)
  have hspan : ∀ y : Fin d → P.R.BdR, (∀ i, y i ∈ (P.PD K).Fil 0) →
      ∃ c : Fin d → P.R.BdR, (∀ j, c j ∈ (P.PD K).Fil (-h j)) ∧ y = ∑ j, c j • (b j : Fin d → P.R.BdR) := by
    intro y hy
    obtain ⟨m, k, bb, z, hz, rfl⟩ := GlobalTheory.T.deRham_filtered_comparison_coordinates l P AI T K d ρ hDR 0 y hy
    have hzD : ∀ r, z r ∈ D := fun r => hIvD _ ((hmemIv _).2 (hz r).1)
    let cf : Fin m → Fin d → ↥K.1 := fun r j => b.repr ⟨z r, hzD r⟩ j
    refine ⟨fun j => ∑ r, cf r j • bb r, fun j => ?_, ?_⟩
    · refine Submodule.sum_mem _ fun r _ => ?_
      by_cases hc : cf r j = 0
      · rw [hc, zero_smul]; exact zero_mem _
      · have hkr := hbrep (k r) ⟨z r, hzD r⟩ ((hmemF _ _).2 (hz r).2.1) j hc
        refine Submodule.smul_mem _ _ (hFil ?_ (hz r).2.2)
        linarith
    · have hexp : ∀ r, z r = ∑ j, cf r j • (b j : Fin d → P.R.BdR) := fun r => by
        have := congrArg Subtype.val (b.sum_repr ⟨z r, hzD r⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      conv_lhs => enter [2, r]; rw [hexp r]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ => ?_
      simp only [Algebra.smul_def]
      ring
  obtain ⟨H, hH⟩ := GlobalTheory.T.hodge_structure_of_adapted_invariant_family l K P AI T C hC ξ hξ d ρ (fun j => (b j : Fin d → P.R.BdR)) h hbinv
    (fun j i => (hmemF _ _).1 (hbF j).1 i) hspan
  refine ⟨H, fun N ⟨h1, h2⟩ i => ?_⟩
  rw [hH i]
  have hne : (b i : Fin d → P.R.BdR) ≠ 0 := fun h0' => b.ne_zero i (Subtype.ext h0')
  obtain ⟨hlo, hhi⟩ := GlobalTheory.T.deRham_filtration_bounds_invariant_coordinates l P K d ρ N h1 h2 _ (hbinv i) hne
  rw [abs_le]
  constructor
  · by_contra hlt
    push_neg at hlt
    exact (hbF i).2 (hF (show h i + 1 ≤ -(N : ℤ) by omega) ((hmemF _ _).2 hlo))
  · by_contra hlt
    push_neg at hlt
    exact hhi ((hmemF _ _).1 (hF (show (N : ℤ) + 1 ≤ h i by omega) (hbF i).1))

end GlobalTheory.HodgeEx
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.HatDescent

variable {l : ℕ} [Fact l.Prime]

theorem aDp_ev_eis_mul_eq_zero {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (y : Per.BdRp l)
    (hy : GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) * y = 0) : y = 0 := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hxi : GlobalTheory.MemLoc.xi ε ∈ Ideal.span {ϖ.ev a (eis l a e)} := by
    rw [ϖ.span_ev_eis a, GlobalTheory.MemLoc.ker_theta_eq_span_xi hE]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hxi
  refine (GlobalTheory.MemLoc.filtration_eq_xi_pow l ε hE).2.1 y ?_
  rw [← hc, map_mul, mul_assoc, hy, mul_zero]

theorem eis_pow_dvd_of_aDp_mem {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (n : ℕ)
    (x : (Wq l a)⟦X⟧)
    (h : GlobalTheory.MemLoc.aDp l (ϖ.ev a x) ∈ Ideal.span {GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) ^ n}) :
    eis l a e ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    have h1 : Per.θ l (ϖ.ev a x) = 0 := by
      have h2 := congrArg (Per.θD l) hc
      rw [map_mul, map_pow, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1,
        (ϖ.theta_ev_eq_zero_iff a _).2 dvd_rfl] at h2
      exact Subtype.ext (h2.symm.trans (by simp))
    obtain ⟨x', rfl⟩ := (ϖ.theta_ev_eq_zero_iff a x).1 h1
    have h2 : GlobalTheory.MemLoc.aDp l (ϖ.ev a x') ∈
        Ideal.span {GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) ^ n} := by
      rw [Ideal.mem_span_singleton']
      refine ⟨c, ?_⟩
      rw [← sub_eq_zero]
      apply aDp_ev_eis_mul_eq_zero (a := a) ϖ
      rw [map_mul, map_mul] at hc
      rw [mul_sub, ← hc]
      ring
    obtain ⟨z, hz⟩ := ih x' h2
    exact ⟨z, by rw [hz, pow_succ']; ring⟩

end GlobalTheory.BKReal.HatDescent

namespace GlobalTheory.BKReal.HatDescent

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

def crdB {J : Type} (b : Module.Basis J ℤ_[l] O) (j : J) : OD l O →ₗ[ℤ_[l]] Per.BdRp l :=
  TensorProduct.lid ℤ_[l] (Per.BdRp l) ∘ₗ (b.coord j).rTensor (Per.BdRp l)

theorem crdB_tmul {J : Type} (b : Module.Basis J ℤ_[l] O) (j : J) (o : O) (β : Per.BdRp l) :
    crdB b j (o ⊗ₜ β) = b.coord j o • β := rfl

theorem crdB_mul {J : Type} (b : Module.Basis J ℤ_[l] O) (j : J) (c : Per.BdRp l) (z : OD l O) :
    crdB b j (z * (1 ⊗ₜ c)) = crdB b j z * c := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o β =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, crdB_tmul, crdB_tmul, smul_mul_assoc]
  | add x y hx hy => rw [add_mul, map_add (f := _), map_add (f := _), hx, hy, add_mul]

theorem crdB_sum {J : Type} [Fintype J] [DecidableEq J] (b : Module.Basis J ℤ_[l] O) (j : J)
    (β : J → Per.BdRp l) : crdB b j (∑ k, b k ⊗ₜ β k) = β j := by

  rw [map_sum, Finset.sum_eq_single j (fun k _ hk => by
  rw [crdB_tmul, Module.Basis.coord_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply, hk])
  (by simp), crdB_tmul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, one_smul]

variable {a e : ℕ} [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem toAc_eis (t : Wq l a →ₐ[ℤ_[l]] O) : toAc t K (eis l a e) = fun _ => EIn l e (A O K) := by
  have hX : toAc t K X = fun _ => uIn (A O K) :=
    funext fun τ => Subtype.ext ((congrArg (PowerSeries.map _) (PowerSeries.map_X _)).trans
      (PowerSeries.map_X _))
  have hE : EIn l e (A O K) = uIn _ ^ e + (l : A O K) := Subtype.ext (by simp [E])
  rw [eis, map_add (f := _), map_pow, hX, map_natCast, hE]
  rfl

theorem exists_of_toOD_iTot_mem (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (n : ℕ) (f : ZMod a → A O K)
    (h : toOD l O (ϖ.iTot t K f) ∈
      Ideal.span {((1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) : OD l O) ^ n}) :
    ∃ g : ZMod a → A O K, f = (fun _ => EIn l e (A O K)) ^ n * g := by
  classical
  set b := Module.Free.chooseBasis ℤ_[l] O
  obtain ⟨x, rfl⟩ := exists_eq_sum_toAc t K b f
  have hT : toOD l O (ϖ.iTot t K (∑ j, b j • toAc t K (x j))) =
      ∑ j, b j ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (x j)) := by

    simp only [map_sum, map_smul, PiSys.iTot_toAc]
    refine Finset.sum_congr rfl fun j _ => ?_
    show b j • ((1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (x j))) = _
    rw [smul_tmul', smul_eq_mul, mul_one]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  have hx : ∀ j, eis l a e ^ n ∣ x j := fun j => by
    apply eis_pow_dvd_of_aDp_mem ϖ n
    rw [Ideal.mem_span_singleton']
    refine ⟨crdB b j z, ?_⟩
    have := congrArg (crdB b j) (hz.trans hT)
    rw [crdB_sum, Algebra.TensorProduct.tmul_pow, one_pow, crdB_mul] at this
    exact this
  choose y hy using hx
  refine ⟨∑ j, b j • toAc t K (y j), ?_⟩
  simp only [hy, map_mul, map_pow, toAc_eis, Finset.mul_sum, mul_smul_comm]

end GlobalTheory.BKReal.HatDescent

namespace GlobalTheory.BKReal.PiSys

open GlobalTheory.BKReal.HatDescent

theorem eq_Ehat_pow_mul_of_iD_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (n : ℕ) (x : ZMod a → Ahat O K l e),
    ϖ.iD t K x ∈ Ideal.span {ϖ.iD t K (fun _ => Ehat O K l e) ^ n} →
      ∃ y : ZMod a → Ahat O K l e, x = (fun _ => Ehat O K l e) ^ n * y := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ n x hx
  have hd : ϖ.iD t K (fun _ => Ehat O K l e) =
      (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) := by
    rw [iD, glue_const, Ehat, iHat_ofAl]
    exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
  choose g x' hg using fun τ => _root_.GlobalTheory.BK.exists_eq_algebraMap_add_pow_mul (EIn l e (invL l (A O K))) n (x τ)
  have hsplit : x = (fun τ => ofAl O K l e (g τ)) + (fun _ => Ehat O K l e) ^ n * x' :=
    funext fun τ => hg τ
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (l : A O K)) (S := invL l (A O K)) g
  choose r hr using hm

  have h1 : ϖ.iD t K (fun τ => ofAl O K l e (g τ)) ∈
      Ideal.span {ϖ.iD t K (fun _ => Ehat O K l e) ^ n} := by
    rw [hsplit, map_add (f := _), map_mul, map_pow] at hx
    exact (Ideal.add_mem_iff_left _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))).1 hx
  have h2 : (fun τ => ofA O K l e (r τ)) =
      (fun _ => ofA O K l e ((l : A O K) ^ m)) * fun τ => ofAl O K l e (g τ) := by
    funext τ
    rw [Pi.mul_apply, ofA, RingHom.comp_apply, RingHom.comp_apply, hr τ, Algebra.smul_def, map_mul]
  have h3 : toOD l O (ϖ.iTot t K r) ∈
      Ideal.span {((1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) : OD l O) ^ n} := by
    rw [← iD_ofA, h2, map_mul, ← hd]
    exact Ideal.mul_mem_left _ _ h1
  obtain ⟨h, hh⟩ := exists_of_toOD_iTot_mem t ϖ n r h3
  have hu : IsUnit (algebraMap (A O K) (invL l (A O K)) (l : A O K)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hEA : algebraMap (A O K) (invL l (A O K)) (EIn l e (A O K)) = EIn l e (invL l (A O K)) := rfl
  have hgτ : ∀ τ, g τ = EIn l e (invL l (A O K)) ^ n *
      (algebraMap (A O K) (invL l (A O K)) (h τ) * ↑(hu.unit⁻¹ ^ m)) := fun τ => by
    have h4 : algebraMap (A O K) (invL l (A O K)) (l : A O K) ^ m * g τ =
        EIn l e (invL l (A O K)) ^ n * algebraMap (A O K) (invL l (A O K)) (h τ) := by
      have h5 := (hr τ).symm
      rw [Algebra.smul_def, hh, Pi.mul_apply, Pi.pow_apply] at h5
      simp only [map_mul, map_pow, hEA] at h5
      exact h5
    have hone : (↑(hu.unit⁻¹ ^ m) : invL l (A O K)) * algebraMap (A O K) (invL l (A O K)) (l : A O K) ^ m = 1 := by
      rw [Units.val_pow_eq_pow_val, ← mul_pow, hu.val_inv_mul, one_pow]
    linear_combination (-(g τ)) * hone + (↑(hu.unit⁻¹ ^ m) : invL l (A O K)) * h4
  refine ⟨fun τ => ofAl O K l e (algebraMap (A O K) (invL l (A O K)) (h τ) * ↑(hu.unit⁻¹ ^ m)) + x' τ, ?_⟩
  funext τ
  rw [hg τ, Pi.mul_apply, Pi.pow_apply, hgτ τ, map_mul, map_pow, mul_add]
  rfl

end GlobalTheory.BKReal.PiSys
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.WDelta

variable {l : ℕ} {A : Type} [CommRing A]

theorem δ_pow_succ (D : Delta l A) (z : A) (m : ℕ) :
    ∃ c, D.δ (z ^ (m + 1)) = ((m + 1 : ℕ) : A) * z ^ (l * m) * D.δ z + (l : A) * D.δ z ^ 2 * c := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨z ^ l * c + ((m + 1 : ℕ) : A) * z ^ (l * m) + (l : A) * D.δ z * c, ?_⟩
    have e1 : (z ^ (m + 1)) ^ l = z ^ (l * m) * z ^ l := by rw [← pow_mul, ← pow_add]; ring_nf
    have e2 : z ^ (l * (m + 1)) = z ^ (l * m) * z ^ l := by rw [← pow_add]; ring_nf
    rw [pow_succ z (m + 1), D.δ_mul, hc, e1, e2]
    push_cast
    ring

theorem δ_pow_pow [hl : Fact l.Prime] (D : Delta l A) (y : A) (n : ℕ) :
    D.δ (y ^ (l ^ n)) ∈ Ideal.span {(l : A)} ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := δ_pow_succ D (y ^ (l ^ n)) (l - 1)
    rw [Nat.sub_add_cancel hl.out.one_le] at hc
    rw [pow_succ l n, pow_mul, hc, pow_succ]
    have : ((l : ℕ) : A) * (y ^ l ^ n) ^ (l * (l - 1)) * D.δ (y ^ l ^ n) + (l : A) * D.δ (y ^ l ^ n) ^ 2 * c =
        D.δ (y ^ l ^ n) * ((l : A) * ((y ^ l ^ n) ^ (l * (l - 1)) + D.δ (y ^ l ^ n) * c)) := by ring
    rw [this]
    exact Ideal.mul_mem_mul ih (Ideal.mem_span_singleton.2 (dvd_mul_right _ _))

theorem eq_zero_of_mem_pow {C : Type} [CommRing C] {J : Ideal C} (h : IsHausdorff J C) {x : C}
    (hx : ∀ n, x ∈ J ^ n) : x = 0 :=
  h.haus x fun n => by rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]; exact hx n

variable (l) (a : ℕ) [hl : Fact l.Prime] [NeZero a]

theorem teich_eq_pow (n : ℕ) (x : Fq l a) :
    ∃ y : Fq l a, WittVector.teichmuller l x = WittVector.teichmuller l y ^ (l ^ n) := by
  induction n with
  | zero => exact ⟨x, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨y ^ (l ^ (a - 1)), ?_⟩
    have h1 : (y ^ (l ^ (a - 1))) ^ l = y := by
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (NeZero.pos a)]; exact Fq.pow_card (l := l) (a := a) y
    rw [hy, pow_succ' l n, pow_mul, ← map_pow (WittVector.teichmuller l) (y ^ l ^ (a - 1)) l, h1]

theorem deltaS_C_teich (x : Fq l a) :
    (deltaS l a).δ (PowerSeries.C (WittVector.teichmuller l x)) = 0 := by
  have h := (deltaS l a).φ_eq (PowerSeries.C (WittVector.teichmuller l x))
  have h2 : (deltaS l a).φ (PowerSeries.C (WittVector.teichmuller l x)) =
      PowerSeries.C (WittVector.teichmuller l x) ^ l := by
    change frobS l a _ = _
    have := sigma_pow_teich l a 1 x
    rw [pow_one, pow_one] at this
    rw [frobS_C, this, map_pow]
  rw [h2, left_eq_add] at h
  exact (mul_eq_zero.1 h).resolve_left (l_ne_zero l a)

variable {l a}

theorem C_teich_mem {C : Type} [CommRing C] (DC : Delta l C) {J : Ideal C} (hl : (l : C) ∈ J)
    (hJ : IsHausdorff J C) (σ : (Wq l a)⟦X⟧ →+* C) (x : Fq l a) :
    PowerSeries.C (WittVector.teichmuller l x) ∈ δLocus (deltaS l a) DC σ := by
  rw [mem_δLocus, deltaS_C_teich, map_zero]
  refine (eq_zero_of_mem_pow hJ fun n => ?_).symm
  obtain ⟨y, hy⟩ := teich_eq_pow l a n x
  rw [hy, map_pow, map_pow]
  exact Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem J).2 hl) n (δ_pow_pow DC _ n)

theorem approx (S : Subring (Wq l a)) (hS : ∀ x, WittVector.teichmuller l x ∈ S) (n : ℕ) (w : Wq l a) :
    ∃ s ∈ S, ∃ v, w - s = (l : Wq l a) ^ n * v := by
  induction n with
  | zero => exact ⟨0, S.zero_mem, w, by simp⟩
  | succ n ih =>
    obtain ⟨s, hs, v, hv⟩ := ih
    have h : v - WittVector.teichmuller l (v.coeff 0) ∈ Ideal.span {(l : Wq l a)} := by
      rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, sub_self]
    obtain ⟨v', hv'⟩ := Ideal.mem_span_singleton.1 h
    refine ⟨s + (l : Wq l a) ^ n * WittVector.teichmuller l (v.coeff 0),
      S.add_mem hs (S.mul_mem (S.pow_mem (natCast_mem S l) n) (hS _)), v', ?_⟩
    rw [pow_succ, mul_assoc, ← hv']
    linear_combination hv

end GlobalTheory.BSP.WDelta

namespace GlobalTheory.BSP


open GlobalTheory.BSP.WDelta in
theorem C_mem_δLocus_of_hausdorff : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Type) [CommRing C]
    (DC : Delta l C) (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ σ : (Wq l a)⟦X⟧ →+* C,
    ∀ w : Wq l a, PowerSeries.C w ∈ δLocus (deltaS l a) DC σ := by
  intro l _ a _ C _ DC J hl hJ σ w
  let S : Subring (Wq l a) := (δLocus (deltaS l a) DC σ).comap PowerSeries.C
  rw [mem_δLocus, ← sub_eq_zero]
  refine eq_zero_of_mem_pow hJ fun n => ?_
  obtain ⟨s, hs, v, hv⟩ := approx S (fun x => C_teich_mem DC hl hJ σ x) (n + 1) w
  have hs' := mem_δLocus.1 (Subring.mem_comap.1 hs)
  have hy : PowerSeries.C w - PowerSeries.C s = (l : (Wq l a)⟦X⟧) ^ (n + 1) * PowerSeries.C v := by
    rw [← map_sub, hv, map_mul, map_pow, map_natCast]
  have h1 := GlobalTheory.T.delta_add_sub_mem_pow_of_mem_pow_succ l (Wq l a)⟦X⟧ (deltaS l a) (Ideal.span {(l : (Wq l a)⟦X⟧)})
    (Ideal.mem_span_singleton_self _) n (PowerSeries.C s) (PowerSeries.C w - PowerSeries.C s)
    (by rw [hy, Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _))
  rw [add_sub_cancel, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  obtain ⟨r, hr⟩ := h1
  have h2 := GlobalTheory.T.delta_add_sub_mem_pow_of_mem_pow_succ l C DC J hl n (σ (PowerSeries.C s)) (σ (PowerSeries.C w - PowerSeries.C s))
    (by rw [hy, map_mul, map_pow, map_natCast]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl _))
  rw [← map_add (f := _), add_sub_cancel] at h2
  have h3 : σ ((deltaS l a).δ (PowerSeries.C w)) - σ ((deltaS l a).δ (PowerSeries.C s)) ∈ J ^ n := by
    rw [← map_sub, hr, map_mul, map_pow, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl _)
  have := (J ^ n).sub_mem h3 h2
  rw [hs'] at this
  convert this using 1
  ring

end GlobalTheory.BSP
end
end
