module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle683
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle706
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle735
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle690
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle758
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle682
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValueMemFiltrationZeroTame
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle604
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle757
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle759
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle185
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.CharsDesc

theorem toBcris_inj {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (hB : Function.Injective (ϖ.iB t K)) :
    Function.Injective (toBcris t ϖ P) := by
  intro m m' h
  have hc : coordL P (invL l (S O K e)) m = coordL P (invL l (S O K e)) m' := by
    funext i
    apply hB
    have := congrFun h i
    rwa [toBcris_apply, toBcris_apply] at this
  apply Subtype.ext
  funext τ
  rw [← mx_mulVec_coordL P _ m τ, ← mx_mulVec_coordL P _ m' τ, hc]

theorem xi_mem_MMl {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (d : P.D) :
    P.xi d ∈ P.MMl := by
  refine ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a ι P).2 (cst d)).2 ?_
  refine mem_tot.2 fun τ i => ?_
  obtain ⟨n, b, hb⟩ := exists_pow_mul_mem (O := O) l (d τ i)
  refine ⟨n, ?_⟩
  have h1 : (((l : S O K e) : K⟦X⟧)) ^ n * cst d τ i = algebraMap O K⟦X⟧ b := by
    rw [IsScalarTower.algebraMap_apply O K K⟦X⟧, ← hb]
    simp [cst]
  rw [h1]
  exact Subalgebra.algebraMap_mem _ b

theorem actD_single {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a] {P : PhiMod O K l e a ι} (Δ : Descent P)
    (ζ : rootsOfUnity e K) (d : P.D) (τ : ZMod a) :
    Δ.actD (TameGal.inertia ζ) (Pi.single τ (d τ) : P.D) = Pi.single τ (Δ.actD (TameGal.inertia ζ) d τ) := by
  classical
  have hf : ringAct (TameGal.inertia ζ : TameGal K l e a) (Pi.single τ 1) = Pi.single τ 1 := by
    funext σ
    rw [ringAct_apply, TameGal.shift_inertia, sub_zero]
    by_cases h : σ = τ
    · subst h; simp
    · simp [h]
  have hc : cst (Pi.single τ (d τ) : P.D) = (Pi.single τ 1 : ZMod a → K⟦X⟧) • cst d := by
    funext σ i
    by_cases h : σ = τ
    · subst h; simp [cst]
    · simp [cst, h]
  have hr : ∀ w : Vec K a ι, red ((Pi.single τ 1 : ZMod a → K⟦X⟧) • w) = Pi.single τ (red w τ) := by
    intro w
    funext σ i
    by_cases h : σ = τ
    · subst h; simp [red, red0]
    · simp [red, red0, h]
  change red (Δ.act _ (cst _)) = _
  rw [hc, Δ.act_smul_tot, hf, hr]
  rfl

private theorem tensor_equiv_map_smul {R A N ι : Type} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup N] [Module R N]
    (j : (ι → A) ≃ₗ[A] A ⊗[R] N) (r : R) (v : ι → A) :
    j (r • v) = r • j v := by
  have : IsScalarTower R A (A ⊗[R] N) := TensorProduct.isScalarTower_left
  calc
    j (r • v) = j (algebraMap R A r • v) :=
      congrArg (fun w => j w) (algebraMap_smul A r v).symm
    _ = algebraMap R A r • j v := j.map_smul _ _
    _ = r • j v := algebraMap_smul A r (j v)

theorem jB_smul {l : ℕ} [Fact l.Prime] {LL : FinExt l} {T : QLat LL} {ι : Type} [Fintype ι]
    (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (o : ↥(OL LL))
    (v : ι → OB l ↥(OL LL)) : jB (o • v) = o • jB v := by
  exact tensor_equiv_map_smul (R := ↥(OL LL)) (A := OB l ↥(OL LL)) (N := ↥T.L.T) jB o v

theorem smul_eq_algebraMap_smul {l : ℕ} [Fact l.Prime] {LL : FinExt l} (T : QLat LL) (Pl : LocPrime l)
    (o : ↥(OL LL)) (x : T.V ⊗[ℚ_[l]] Pl.R.B) : o • x = (algebraMap ↥(OL LL) ↥LL.1 o) • x :=
  (algebraMap_smul (↥LL.1) o x).symm

theorem mem_Dcris_res {l : ℕ} [Fact l.Prime] {LL : FinExt l} (T : QLat LL) (Pl : LocPrime l) (F : FinExt l)
    (x : (resF T F).V ⊗[ℚ_[l]] Pl.R.B)
    (h : ∀ g : ↥(GK F), actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ (inclG F g) (x : T.V ⊗[ℚ_[l]] Pl.R.B) = x) :
    x ∈ Dcris (Pl.PD F) (resF T F).ρ := by
  refine (Submodule.mem_iInf _).2 fun g => LinearMap.mem_ker.2 (sub_eq_zero.2 ?_)
  have key : actVB (Pl.PD F) (resF T F).ρ g = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ (inclG F g) := by
    unfold actVB
    congr 1
    ext b
    exact (Pl.PD_actB F g b).trans (Pl.PD_actB _ (inclG F g) b).symm
  exact (LinearMap.congr_fun key x).trans (h g)

end GlobalTheory.CharsDesc

private theorem eval_eq_zero_of_aeval_eq_zero {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {f : Module.End K V} {p : Polynomial K} {x : V} {z : K}
    (hx : x ≠ 0) (h : f x = z • x) (hp : Polynomial.aeval f p x = 0) : p.eval z = 0 :=
  (smul_eq_zero.mp ((Module.End.aeval_apply_of_mem_apply_eq_smul h).symm.trans hp)).resolve_right hx

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 8000000 in
open GlobalTheory.CharsDesc in
theorem GlobalTheory.CharsDesc.chars_subset_sig : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Δ : Descent P) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → IsGalDesc (sQ l) I Δ → ∀ Sig : Finset (ZMod e), TameType a ϖ Pl T Sig → ∀ τ, Δ.chars τ ⊆ (Sig : Set (ZMod e)) := by
  intro l _ a e _ _ ϖ LL _ _ _ ι _ _ P T I jB Δ Pl AI hStd hCmp hHor hDesc Sig hType τ c hc
  have hpoly : ∀ (z : ↥LL.1) (n : ℕ),
      (∏ j ∈ Sig, (Polynomial.X - Polynomial.C (z ^ j.val)) : Polynomial ↥LL.1).eval (z ^ n) = 0 →
      ∃ j ∈ Sig, z ^ n = z ^ j.val := by
    intro z n h
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Finset.prod_eq_zero_iff, sub_eq_zero] at h
    exact h
  have hc0 : c ∈ Δ.chars 0 := by
    rw [← (GlobalTheory.T.tameDescent_characters_eq_and_frobenius_stable _ _ l e a ι P Δ).1 τ 0]; exact hc
  obtain ⟨d, hd0, hdc⟩ := hc0

  obtain ⟨ζ, hζ⟩ := TameDescentExponentData.prim (K := ↥LL.1) (l := l) (e := e) (a := a)
  obtain ⟨ζu, hζu⟩ : ∃ ζu : rootsOfUnity e ↥LL.1, (((ζu : (↥LL.1)ˣ) : ↥LL.1)) = ζ := ⟨hζ.toRootsOfUnity, rfl⟩
  have I8 := GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL
  obtain ⟨k, -, hkc⟩ := I8.2.2.1 (TameGal.inertia ζu)
  obtain ⟨k', hk'I, hk'c, hk'π⟩ := I8.2.2.2.2.2.2 k ζu hkc
  classical
  obtain ⟨d', hd'_def⟩ : ∃ d' : P.D, d' = Pi.single 0 (d 0) := ⟨_, rfl⟩
  have hd'0 : d' ≠ 0 := by
    intro h; apply hd0; have := congrFun h 0; rw [hd'_def, Pi.single_eq_same] at this; exact this
  have hact' : Δ.actD (TameGal.inertia ζu) d' = (ζ ^ c.val) • d' := by
    rw [hd'_def, actD_single, hdc ζu, TameGal.root_inertia_zero, hζu, Pi.single_smul]
  have hm := xi_mem_MMl P d'
  let σ : P.MMl := ⟨P.xi d', hm⟩
  have hnorm : ‖ζ ^ c.val‖ ≤ 1 := by
    have h1 : ‖ζ‖ = 1 := by
      have h := congrArg norm hζ.pow_eq_one
      rw [norm_pow, norm_one] at h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne e)).1 h
    rw [norm_pow, h1, one_pow]
  obtain ⟨o, ho⟩ := (IsUnitBall.mem_range_iff (O := ↥(OL LL)) (ζ ^ c.val)).2 hnorm
  let latticeSMul : SMul ↥(OL LL) P.MMl := inferInstance
  let σ' := latticeSMul.smul o σ
  have hσ' : σ'.1 = Δ.act (TameGal.inertia ζu) σ.1 := by
    change o • P.xi d' = Δ.act (TameGal.inertia ζu) (P.xi d')
    rw [Descent.act_xi, hact', P.xi.map_smul, ← ho, algebraMap_smul]
  let f := toBcris (thetaW a LL) ϖ P
  let b := jB (f σ)
  have hA := GlobalTheory.T.kisinInfGalois_acts_through_descentDatum l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P T I jB Δ hCmp hDesc k'
    (TameGal.inertia ζu) hk'c σ σ' hσ'
  obtain ⟨β, -, hβ2, -, -⟩ := GlobalTheory.T.exists_bcrisTensorLattice_equiv_periodRing l LL T Pl AI hStd
  let x := β b
  have hx0 : x ≠ 0 := by
    intro h
    have hb0 : b = 0 := β.map_eq_zero_iff.mp h
    have hf0 : f σ = 0 := jB.map_eq_zero_iff.mp hb0
    have hσ0 : σ = 0 := toBcris_inj (thetaW a LL) ϖ P
      (GlobalTheory.T.embeddingProductSeriesToTensorBcris_injective_finExt l a e LL (thetaW a LL) ϖ)
      (hf0.trans (map_zero f).symm)
    have hxi0 : P.xi d' = 0 := congrArg Subtype.val hσ0
    exact hd'0 ((P.red_xi d').symm.trans ((congrArg (fun v => red v) hxi0).trans red.map_zero))
  have hxD : x ∈ Dcris (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ := by
    refine mem_Dcris_res T Pl (ϖ.field a) x fun g => ?_
    have hfixed : actB (sQ l) T (inclG (ϖ.field a) g) b = b :=
      hHor (inclG (ϖ.field a) g) g.2 d' hm
    exact (hβ2 (inclG (ϖ.field a) g) b).symm.trans (congrArg (fun w => β w) hfixed)
  have hact : (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ k' : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) x =
      (ζ ^ c.val) • x := by
    have hb := (congrArg (fun v => jB v) (f.map_smul o σ)).trans (jB_smul jB o (f σ))
    have hβo := (β.map_smul o b).trans (smul_eq_algebraMap_smul T Pl o x)
    exact (hβ2 k' b).symm.trans <| (congrArg (fun w => β w) (hA.trans hb)).trans <|
      hβo.trans (congrArg (fun s : ↥LL.1 => s • x) ho)
  have hk'π' : ((ζ : ↥LL.1) : Om l) * ϖ.seq 0 = (k' : GQ l) (ϖ.seq 0) := by rw [← hζu]; exact hk'π
  have hT := hType k' hk'I ζ hk'π' x hxD
  obtain ⟨c', hc', hcc⟩ := hpoly ζ c.val (eval_eq_zero_of_aeval_eq_zero hx0 hact hT)
  have hval := hζ.pow_inj (ZMod.val_lt c) (ZMod.val_lt c') hcc
  rw [ZMod.val_injective e hval]
  exact hc'
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


open GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.ValueFil in
theorem GlobalTheory.BKGal.XiFil.xi_value_gal_sub_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∃ m₀ : ℕ, ∀ w ∈ D.Mext (invL l (A O K)), (∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m₀ * h) → ∀ (hw : D.xiExt w ∈ D.MMl) (g : Gl l), sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩)) - R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ ι _ _ η H D T R
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (l := l) (e := e) (a := a)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  refine ⟨η, fun w hwA hN hw g hg C => ?_⟩
  have hwS : ∀ τ j, w τ j ∈ invL l (S O K e) := fun τ j =>
    away_mono (A_le_S l e) (by simp) (mem_tot.1 hwA τ j)
  have hd : ∀ j : ι, D.xi (fun _ => Pi.single j (1 : K)) ∈ D.MMl := fun j =>
    ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a ι D.toPhiMod).2 _).2 (mem_tot.2 fun τ i => by
      rw [cst_apply]
      exact HasK.C_mem _)
  obtain ⟨V, hV⟩ : ∃ V : ι → TW (OB l O) T,
      V = fun j => R.jB (toBcris t ϖ D.toPhiMod ⟨D.xi (fun _ => Pi.single j 1), hd j⟩) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ι → OB l O, c = fun j => ϖ.iB t K (fun τ => ⟨w τ j, hwS τ j⟩) := ⟨_, rfl⟩
  have hval : R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩) = ∑ j, c j • V j := by

    rw [GlobalTheory.T.tensorBcris_frobenius_value_eq_sum_coordinates l a e O K t ϖ ι D.toPhiMod w hwS hw hd, map_sum, hV, hc]
    simp only [map_smul]
  have hfix : ∀ j, actB (sQ l) T g (V j) = V j := fun j => by
    rw [hV]
    exact R.horiz g hg _ (hd j)
  have hgval : actB (sQ l) T g (∑ j, c j • V j) = ∑ j, galOB O (sQ l g) (c j) • V j := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change TWact (galOB O (sQ l g)) T g (c j • V j) = _
    rw [TWact_smul]
    change _ • actB (sQ l) T g (V j) = _
    rw [hfix j]
  rw [hval, hgval, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← sub_smul]
  have h1 : galOB O (sQ l g) (c j) - c j ∈ filO O C η := by
    rw [hc]
    refine GlobalTheory.T.galOB_iB_sub_iB_mem_filO l a e O K t ϖ C η (fun τ => ⟨w τ j, hwS τ j⟩) (fun τ => mem_tot.1 hwA τ j)
      (fun τ => ?_) g hg
    obtain ⟨h, hh, k, hk⟩ := hN τ j
    exact ⟨h, hh, k, hk⟩
  have h2 : V j ∈ filT C T (-(η : ℤ)) := by
    rw [hV]
    dsimp only
    obtain ⟨u, hu⟩ : ∃ u, u = toBcris t ϖ D.toPhiMod ⟨D.xi (fun _ => Pi.single j 1), hd j⟩ := ⟨_, rfl⟩
    rw [← hu]
    have hsum : u = ∑ i, u i • Pi.single i (1 : OB l O) := by
      ext1 k
      simp [Finset.sum_apply, Pi.single_apply]

    rw [hsum, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    refine smul_mem_filT_of_zero ?_ (GlobalTheory.T.jB_single_mem_filT' l a e O K t ϖ ι η H D T R C i)
    rw [hu, toBcris_apply]
    exact GlobalTheory.T.invariant_lattice_filtration_zero l a e O K t ϖ C _
  exact smul_mem_filT_neg h1 h2
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.PackMap

section General

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {G : Type} [Group G] [TopologicalSpace G]

theorem latW_TWact {T T' : LocLat G ℚ_[l] K O} (f : LatHom T.L T'.L) (s : GQ l) (g : G)
    (y : TW (OW l O) T) :
    latW f (TWact (galOW O s) T g y) = TWact (galOW O s) T' g (latW f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x =>
    simp only [latW, TWact, TensorProduct.map_tmul]
    congr 1
    exact Subtype.ext (f.equiv g x)
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem homW_act {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat G ℚ_[l] K O}
    {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {f : LatHom T.L T'.L} {F : BK.Hom P Q}
    (h : IsMapOf I I' f F) (s : GQ l) (g : G) (v : ι → OW l O) :
    homW t ϖ F (I.act s g v) = I'.act s g (homW t ϖ F v) :=
  I'.j.injective (by rw [h, I.j_act, latW_TWact, I'.j_act, h])

variable [TameDescentExponentData K l e a]

theorem app_act_of_cover {s : G →* GQ l} {η H η' H' : ℕ} {D₁ : BKDat O K l e a ι η H}
    {D₂ : BKDat O K l e a κ η' H'} {T₁ T₂ : LocLat G ℚ_[l] K O} (R₁ : GalDat t ϖ s D₁ T₁)
    (R₂ : GalDat t ϖ s D₂ T₂) {f : LatHom T₁.L T₂.L} {F : BK.Hom D₁.toPhiMod D₂.toPhiMod}
    (hF : IsMapOf R₁.I R₂.I f F) (hcov : ∀ γ : TameGal K l e a, ∃ g : G, Covers K t ϖ (s g) γ)
    (γ : TameGal K l e a) (v : Vec K a ι) :
    F.app (D₁.desc.act γ v) = D₂.desc.act γ (F.app v) := by
  have hb : ∀ i : ι, F.app (D₁.desc.act γ (bas i)) = D₂.desc.act γ (F.app (bas i)) := by
    intro i
    obtain ⟨g, hg⟩ := hcov γ
    have m0 : (bas i : Vec K a ι) ∈ D₁.M := PhiMod.bas_mem_M _ i
    have m1 : D₁.desc.act γ (bas i) ∈ D₁.M := D₁.desc.act_mem_M γ _ m0
    have m2 : F.app (bas i) ∈ D₂.M := F.app_mem_M m0
    have m3 : D₂.desc.act γ (F.app (bas i)) ∈ D₂.M := D₂.desc.act_mem_M γ _ m2
    have m4 : F.app (D₁.desc.act γ (bas i)) ∈ D₂.M := F.app_mem_M m1
    have e1 := R₁.desc g γ hg ⟨_, mem_ME_of_mem_M m0⟩ ⟨_, mem_ME_of_mem_M m1⟩ rfl
    have e2 := R₂.desc g γ hg ⟨_, mem_ME_of_mem_M m2⟩ ⟨_, mem_ME_of_mem_M m3⟩ rfl
    have h1 := homW_toW t ϖ F ⟨_, mem_ME_of_mem_M m1⟩
    have h2 := homW_toW t ϖ F ⟨_, mem_ME_of_mem_M m0⟩
    have key : toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m4⟩ =
        toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m3⟩ :=
      calc toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m4⟩
          = homW t ϖ F (toW t ϖ D₁.toPhiMod ⟨_, mem_ME_of_mem_M m1⟩) := h1.symm
        _ = homW t ϖ F (R₁.I.act (s g) g (toW t ϖ D₁.toPhiMod ⟨_, mem_ME_of_mem_M m0⟩)) := by rw [e1]
        _ = R₂.I.act (s g) g (homW t ϖ F (toW t ϖ D₁.toPhiMod ⟨_, mem_ME_of_mem_M m0⟩)) :=
          homW_act hF _ _ _
        _ = R₂.I.act (s g) g (toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m2⟩) := by rw [h2]
        _ = toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m3⟩ := e2
    exact congrArg Subtype.val (toW_injective t ϖ _ key)

  rw [eq_sum_bas v, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [D₁.desc.act_smul_tot, F.app_smul_tot, F.app_smul_tot, D₂.desc.act_smul_tot, hb]

end General

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (T₁ T₂ : QLat LL)
    (P₁ : Pack a ϖ η H T₁) (P₂ : Pack a ϖ η H T₂) (f : LatHom T₁.L T₂.L),
    ∃ F : BKHom P₁.D P₂.D, IsMapOf P₁.R.I P₂.R.I f F.toHom := by
  intro BS l _ a e _ _ ϖ LL _ _ η H T₁ T₂ P₁ P₂ f
  let f' : LatHom (resF T₁ (ϖ.field a)).L (resF T₂ (ϖ.field a)).L :=
    ⟨f.f, fun _ x => f.equiv _ x, f.cont, f.T_le⟩
  obtain ⟨F, hF⟩ := GlobalTheory.BKReal.Full.main BS l a e _ _ (thetaW a LL) ϖ _ _ P₁.D.toPhiMod P₂.D.toPhiMod
    (resF T₁ (ϖ.field a)) (resF T₂ (ϖ.field a))
    (P₁.R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _))
    (P₂.R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) P₁.isBK P₂.isBK f'
  have hF' : IsMapOf P₁.R.I P₂.R.I f F := hF
  have hcov : ∀ γ : TameGal ↥LL.1 l e a, ∃ g : Gl l, Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ := fun γ => by
    obtain ⟨k, -, hc⟩ := (GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL).2.2.1 γ
    refine ⟨⟨k, ?_⟩, hc⟩
    show k ∈ (⊥ : IntermediateField ℚ_[l] (Om l)).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    trivial
  exact ⟨⟨F, app_act_of_cover P₁.R P₂.R hF' hcov⟩, hF'⟩

end GlobalTheory.BKGal.PackMap
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.UnitDatum


set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (Pk : Pack a ϖ η H (unitLat (Gl l) : QLat LL)), ∃ (u : ME Pk.D.toPhiMod) (x : ↥(unitLat (Gl l) : QLat LL).L.T), x.1 = (1 : ↥LL.1) ∧ u.1 ∈ Pk.D.Minv ∧ Pk.D.phi u.1 = u.1 ∧ toW (thetaW a LL) ϖ Pk.D.toPhiMod u = Pk.R.I.ofT x := by
  intro BS l _ a e _ _ ϖ LL _ _ η H Pk
  have hx : ((1 : ↥LL.1) : (unitLat (Gl l) : QLat LL).V) ∈ (unitLat (Gl l) : QLat LL).L.T := ⟨1, by simp⟩
  let x : ↥(unitLat (Gl l) : QLat LL).L.T := ⟨(1 : ↥LL.1), hx⟩
  let x' : ↥(resF (unitLat (Gl l) : QLat LL) (ϖ.field a)).L.T := ⟨(1 : ↥LL.1), hx⟩
  have hTriv : IsTriv (resF (unitLat (Gl l) : QLat LL) (ϖ.field a)) := fun _ _ => rfl
  let b : Module.Basis Unit ↥(OL LL) ↥(resF (unitLat (Gl l) : QLat LL) (ϖ.field a)).L.T :=
    ⟨(LinearEquiv.ofInjective (Algebra.linearMap ↥(OL LL) ↥LL.1) IsUnitBall.inj).symm.trans
      (Finsupp.LinearEquiv.finsuppUnique _ _ _).symm⟩
  have hb : b () = x' := by
    apply Subtype.ext
    change Algebra.linearMap ↥(OL LL) ↥LL.1 ((Finsupp.LinearEquiv.finsuppUnique ↥(OL LL) ↥(OL LL) Unit) (Finsupp.single () 1)) = 1
    rw [show (Finsupp.LinearEquiv.finsuppUnique ↥(OL LL) ↥(OL LL) Unit) (Finsupp.single () 1) = 1 from Finsupp.single_eq_same]
    simp
  have hBK := isBK_unitIdent (thetaW a LL) ϖ hTriv b
  have hBK' := Pk.isBK
  have h1 := GlobalTheory.BKReal.Full.main BS l a e (↥(OL LL)) (↥LL.1) (thetaW a LL) ϖ Unit (Fin Pk.n)
    (unitMod l a e ↥(OL LL) ↥LL.1 Unit) Pk.D.toPhiMod
  have h2 := h1 (resF (unitLat (Gl l) : QLat LL) (ϖ.field a)) (resF (unitLat (Gl l) : QLat LL) (ϖ.field a))
    (unitIdent (thetaW a LL) ϖ _ b)
  have h3 := h2 (Pk.R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _))
  have h4 := h3 hBK
  have h5 := h4 hBK' (latId _)
  obtain ⟨F, hF⟩ := h5
  have hev : (fun _ _ => (1 : (↥LL.1)⟦X⟧) : Vec (↥LL.1) a Unit) ∈ (unitMod l a e ↥(OL LL) ↥LL.1 Unit).M :=
    mem_tot.2 fun _ _ => one_mem _
  have huM : F.app (fun _ _ => (1 : (↥LL.1)⟦X⟧) : Vec (↥LL.1) a Unit) ∈ Pk.D.M := F.app_mem_M hev
  let u : ME Pk.D.toPhiMod := ⟨_, mem_ME_of_mem_M huM⟩
  have h0 : toW (thetaW a LL) ϖ (unitMod l a e ↥(OL LL) ↥LL.1 Unit) ⟨_, mem_ME_of_mem_M hev⟩ =
      (unitIdent (thetaW a LL) ϖ _ b).ofT x' := by
    apply (unitIdent (thetaW a LL) ϖ _ b).j.injective
    refine Eq.trans ?_ ((unitIdent (thetaW a LL) ϖ _ b).j_ofT x').symm
    rw [unitIdent_j, Fintype.sum_unique, hb]
    congr 1
    rw [toW_apply, ← map_one (ϖ.iW (thetaW a LL) ↥LL.1)]
    exact congrArg _ (funext fun _ => Subtype.ext rfl)
  have h6 := homW_toW (thetaW a LL) ϖ F ⟨_, mem_ME_of_mem_M hev⟩
  have key : toW (thetaW a LL) ϖ Pk.D.toPhiMod u = Pk.R.I.ofT x :=
    h6.symm.trans ((congrArg (homW (thetaW a LL) ϖ F) h0).trans (IsMapOf.homW_ofT hF x'))
  refine ⟨u, x, rfl, (Descent.mem_invOf _).2 ⟨huM, fun γ => ?_⟩, ?_, key⟩
  · obtain ⟨k, -, hk⟩ := (GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL).2.2.1 γ
    have hkG : k ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
      intro y
      obtain ⟨y, hy⟩ := y
      obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hy
      exact k.commutes c
    have hv' : Pk.D.desc.act γ u.1 ∈ ME Pk.D.toPhiMod := mem_ME_of_mem_M (Pk.D.desc.act_mem_M γ _ huM)
    have h := Pk.R.desc ⟨k, hkG⟩ γ hk u ⟨_, hv'⟩ rfl
    have hx' : (unitLat (Gl l) : QLat LL).actT ⟨k, hkG⟩ x = x := Subtype.ext rfl
    have h10 : toW (thetaW a LL) ϖ Pk.D.toPhiMod ⟨_, hv'⟩ = toW (thetaW a LL) ϖ Pk.D.toPhiMod u :=
      h.symm.trans ((congrArg (Pk.R.I.act (sQ l ⟨k, hkG⟩) ⟨k, hkG⟩) key).trans
        ((Pk.R.I.act_ofT (sQ l ⟨k, hkG⟩) ⟨k, hkG⟩ x).trans ((congrArg Pk.R.I.ofT hx').trans key.symm)))
    exact congrArg Subtype.val (toW_injective (thetaW a LL) ϖ Pk.D.toPhiMod h10)
  · have h7 := toW_phi (thetaW a LL) ϖ Pk.D.toPhiMod huM
    have h8 : phiW (thetaW a LL) ϖ Pk.D.toPhiMod (Pk.R.I.ofT x) = Pk.R.I.ofT x := by
      rw [← mem_Treal, ← Pk.R.I.range_ofT]
      exact LinearMap.mem_range_self Pk.R.I.ofT x
    have h9 : toW (thetaW a LL) ϖ Pk.D.toPhiMod ⟨Pk.D.phi u.1, mem_ME_of_mem_L (Pk.D.phi_mem_L huM)⟩ =
        toW (thetaW a LL) ϖ Pk.D.toPhiMod u :=
      h7.trans ((congrArg (phiW (thetaW a LL) ϖ Pk.D.toPhiMod) key).trans (h8.trans key.symm))
    exact congrArg Subtype.val (toW_injective (thetaW a LL) ϖ Pk.D.toPhiMod h9)

end GlobalTheory.BKGal.UnitDatum
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.theta_galois_fixed_of_congr_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (x : Per.BdRp l) (M k : ℕ) (s : bk.S), (l : Per.BdRp l) ^ k * aDp l (bk.ev bk.E) ^ M * x - aDp l (bk.ev s) ∈ Per.FilP l (M + 1) → ∀ g : ↥(GK K), Per.σC (g : GQ l) (Per.θD l x) = Per.θD l x := by
  first | exact @GlobalTheory.BKLim.theta_gal_fixed_of_congr | exact GlobalTheory.BKLim.theta_gal_fixed_of_congr | (intros; apply GlobalTheory.BKLim.theta_gal_fixed_of_congr <;> assumption)
end
