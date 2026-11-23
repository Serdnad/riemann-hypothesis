module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnSymmetricLevelAtTypePrime
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle183
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle065
public import Formalism.LocalToGlobal.HermitianForms.PrkSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle185
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
public import Formalism.LocalToGlobal.Columns.PolyFn
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.rowType_mul_on_symmetricLevel_at_typePrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), j < R.m → P ∈ Pr.vGs → ∀ g ∈ Jat (Pr := Pr) (R := R) true j P, ∀ g' ∈ Jat (Pr := Pr) (R := R) true j P, lamRow Ch mu true j P (g * g').toLinearMap = lamRow Ch mu true j P g.toLinearMap * lamRow Ch mu true j P g'.toLinearMap := by
  first | exact @GlobalTheory.SymLevelMul.lamRow_mul | exact GlobalTheory.SymLevelMul.lamRow_mul | (intros; apply GlobalTheory.SymLevelMul.lamRow_mul <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.LevelHecke

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix
open scoped TensorProduct Pointwise

section Span

variable {D : D7} {n : ℕ}

theorem ratSpan_smul (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    {P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hP : P ∈ RatSpan D lam) :
    D.what₂.embLL r • P ∈ RatSpan D lam := by
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r', f, hf, rfl⟩ := hp
    exact AddSubgroup.subset_closure ⟨r * r', f, hf, by rw [smul_smul, map_mul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem map_embLL_smul {σ : Type} (r : D.what₂.LL) (F : MvPolynomial σ D.what₂.LL) :
    MvPolynomial.map D.what₂.embLL (r • F) = D.what₂.embLL r • MvPolynomial.map D.what₂.embLL F := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

theorem exists_of_mem_ratSpan (lam : D.what₂.Tau → DomWeight n)
    {P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hP : P ∈ RatSpan D lam) :
    ∃ F ∈ Formalism.L2.DIV.VV D.what₂.LL lam, MvPolynomial.map D.what₂.embLL F = P := by
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, hf, rfl⟩ := hp
    refine ⟨r • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb D.what₂.LL τ (MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)),
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩), ?_⟩
    · exact Formalism.GradedWeylDivisibility.weylLeDual _ n n le_rfl _ (Formalism.L2.Col.natW_anti (lam τ)) (Formalism.L2.Col.map_mem_weyl le_rfl _ _ (hf τ))
    · rw [map_embLL_smul, Formalism.L2.Col.map_ten]
      congr 2
      funext τ
      rw [MvPolynomial.map_map]
      congr 2
      exact RingHom.ext_int _ _
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, rfl⟩ := hx
    obtain ⟨G, hG, rfl⟩ := hy
    exact ⟨F + G, add_mem hF hG, map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    exact ⟨-F, neg_mem hF, map_neg _ _⟩

theorem map_mem_ratSpan (lam : D.what₂.Tau → DomWeight n)
    {F : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL} (hF : F ∈ Formalism.L2.DIV.VV D.what₂.LL lam) :
    MvPolynomial.map D.what₂.embLL F ∈ RatSpan D lam := by
  classical
  haveI : CharZero D.what₂.LL := D.what₂.embLL.charZero
  let S : D.what₂.Tau → Set (MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL) := fun τ =>
    Set.range fun w : List (Fin n × Fin n × ℕ) =>
      MvPolynomial.rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.applyWord D.what₂.LL w (Formalism.GradedWeylDivisibility.hw D.what₂.LL le_rfl (lam τ).natW))
  have hle : Formalism.L2.DIV.VV D.what₂.LL lam ≤ Submodule.span D.what₂.LL (∏ τ, S τ) := by
    unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have h1 : ∀ τ, MvPolynomial.rename (Prod.mk τ) (f τ) ∈ Submodule.span D.what₂.LL (S τ) := by
      intro τ
      have hf' : f τ ∈ delSq D.what₂.LL n (lam τ) := by
        rw [← Formalism.L2.Col.nablaSq_eq_delSq]; exact hf τ
      have h := Submodule.mem_map_of_mem (f := (MvPolynomial.rename (R := D.what₂.LL)
        (Prod.mk τ : Fin n × Fin n → D.what₂.Tau × Fin n × Fin n)).toLinearMap) hf'
      unfold delSq Formalism.GradedWeylDivisibility.weyl at h
      rw [Submodule.map_span, ← Set.range_comp] at h
      exact h
    rw [← Submodule.prod_span]
    exact Formalism.L2.Col.prod_mem_prod_sub _ _ _ fun τ _ => h1 τ
  have hF' := hle hF
  clear hF
  induction hF' using Submodule.span_induction with
  | mem x hx =>
    rw [Set.mem_finsetProd] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    have hg' : ∀ τ, ∃ w : List (Fin n × Fin n × ℕ),
        MvPolynomial.rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.applyWord D.what₂.LL w (Formalism.GradedWeylDivisibility.hw D.what₂.LL le_rfl (lam τ).natW)) = g τ :=
      fun τ => hg (Finset.mem_univ τ)
    choose w hw using hg'
    refine AddSubgroup.subset_closure ⟨1, fun τ => Formalism.GradedWeylDivisibility.applyWord ℤ (w τ) (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW),
      fun τ => Submodule.subset_span ⟨w τ, rfl⟩, ?_⟩
    rw [map_one, one_smul, map_prod, ten]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← hw τ, MvPolynomial.map_rename, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map,
      ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_embLL_smul]; exact ratSpan_smul lam c hx

theorem ratSpan_blockAct (lam : D.what₂.Tau → DomWeight n) (g : D.what₂.Tau → Matrix (Fin n) (Fin n) D.what₂.LL)
    {P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hP : P ∈ RatSpan D lam) :
    Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (g τ).map D.what₂.embLL) P ∈ RatSpan D lam := by
  obtain ⟨F, hF, rfl⟩ := exists_of_mem_ratSpan lam hP
  rw [← Formalism.L2.Col.map_blockAct]
  apply map_mem_ratSpan
  exact (Formalism.GradedWeylDivisibility.blockActTensor D.what₂.LL D.what₂.LL D.what₂.Tau n n g).2 (fun τ => nablaSq D.what₂.LL n (lam τ))
    (fun τ => nablaSq D.what₂.LL n (lam τ)) (fun τ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable D.what₂.LL n n _ _ f hf) F hF

theorem exists_ratSpan_fnOf_atInf (lam : D.what₂.Tau → DomWeight n) (G : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (s : D.what₂.Tau → ℤ) (γ : Matrix (Fin n) (Fin n) D.host.E)
    {P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hP : P ∈ RatSpan D lam) :
    ∃ Q ∈ RatSpan D lam, fnOf G s (atInf (embT D) γ) P = fnOf G s 1 Q := by
  let g : D.what₂.Tau → Matrix (Fin n) (Fin n) D.what₂.LL := fun τ =>
    γ.map fun a => D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) a)
  have hg : atInf (embT D) γ = fun τ => (g τ).map D.what₂.embLL := by
    funext τ
    ext a b
    exact bwA_embT_eq D τ (γ a b)
  refine ⟨D.what₂.embLL (∏ τ, (g τ).det ^ s τ) • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (g τ).map D.what₂.embLL) P,
    ratSpan_smul lam _ (ratSpan_blockAct lam g hP), ?_⟩
  have h := Formalism.L2.Col.fnOf_mul G s (fun τ => (g τ).map D.what₂.embLL) 1 P
  simp only [Pi.one_apply, Matrix.mul_one] at h
  rw [hg, h, map_prod]
  simp only [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]

end Span



theorem chi_mem_range {D : D7} {u : D.what₂.Word} (T : Forms0 D u)
    (h : ∀ i v h x, ∃ r : D.what₂.LL, D.what₂.embLL r = T.gl.psi0 i v h x) (κ : T.cls0.lev.U) :
    ((T.cls0.lev.chi κ : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  rw [T.glev0.chi_eq κ]
  refine prod_mem fun i _ => ?_
  refine finprod_induction (fun z : ℂ => z ∈ D.what₂.embLL.fieldRange) (one_mem _) (fun _ _ hx hy => mul_mem hx hy) fun v => ?_
  refine finprod_induction (fun z : ℂ => z ∈ D.what₂.embLL.fieldRange) (one_mem _) (fun _ _ hx hy => mul_mem hx hy) fun hv => ?_
  refine inv_mem ?_
  unfold lamJ
  rw [Finset.range_zero, Finset.prod_empty, mul_one]
  exact h i v hv _



theorem uop_rat (D : D7) (u : D.what₂.Word) (T : Forms0 D u)
    (h : ∀ i v h x, ∃ r : D.what₂.LL, D.what₂.embLL r = T.gl.psi0 i v h x)
    (v : (D.mem u).A.vT) (x : ((D.fm u).lat 0).V)
    (hFi : LT.Uop D u 0 v ((D.fm u).emb 0 x) ∈ (D.fm u).Fi 0) :
    ∃ y, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x) := by
  classical
  refine (T.val0.rat _).2 ⟨hFi, fun c => ?_⟩
  have hx := ((T.val0.rat _).1 ⟨x, rfl⟩).2
  have key : ∀ w : (D.fm u).lv 0 v c, (D.fm u).fv 0 v c w = 1 → ∃ P ∈ RatSpan D ((D.fm u).lam 0), ∀ z,
      (D.fm u).upT 0 v c w ((D.fm u).emb 0 x ((D.fm u).up 0 v c w)) z =
        fnOf _ (shiftOf (lamT u 0)) 1 P (T.val0.eY z) := by
    intro w hw
    obtain ⟨z, rfl⟩ := T.lv0.pr_surj v c w
    obtain ⟨γ, η, κ, -, -, -, -, -, hT⟩ := T.up_natural_level_zero v c z hw
    obtain ⟨P, hP, hPe⟩ := hx ((D.fm u).up 0 v c (T.lv0.pr v c z))
    obtain ⟨Q, hQ, hQe⟩ := exists_ratSpan_fnOf_atInf ((D.fm u).lam 0)
      (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0)) (γ.1⁻¹).1 hP
    obtain ⟨r, hr⟩ := chi_mem_range T h κ⁻¹
    refine ⟨D.what₂.embLL r • Q, ratSpan_smul _ r hQ, fun s => ?_⟩
    let y' : Fr D 0 (Nat.zero_le _) := (T.val0.eY s).tr _ (isUnit_det_atInf (embT D) γ.1⁻¹)
    have htr : IsTr (atInf (embT D) γ.1.1) (T.val0.eY (T.val0.eY.symm y')) (T.val0.eY s) := by
      rw [Equiv.apply_symm_apply]
      intro τ
      show (T.val0.eY s).1 τ = atInf (embT D) γ.1.1 τ * (atInf (embT D) (γ.1⁻¹).1 τ * (T.val0.eY s).1 τ)
      rw [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]
    rw [hT _ s _ htr, hPe, Equiv.apply_symm_apply,
      Formalism.L2.Col.fnOf_tr (shiftOf (lamT u 0)) 1 (atInf (embT D) (γ.1⁻¹).1) P y' (T.val0.eY s) (fun τ => rfl),
      map_smul, Pi.smul_apply, smul_eq_mul, ← hQe, hr, map_inv]
    simp only [Pi.one_apply, Matrix.one_mul]
  choose! P hP hPe using key
  refine ⟨∑ w ∈ Finset.univ.filter (fun w : (D.fm u).lv 0 v c => (D.fm u).fv 0 v c w = 1), P w,
    sum_mem fun w hw => hP w (Finset.mem_filter.1 hw).2, fun z => ?_⟩

  rw [map_sum, Finset.sum_apply]
  simp only [LT.Uop, LinearMap.pi_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearEquiv.coe_coe]
  convert Finset.sum_congr rfl fun w hw => hPe w (Finset.mem_filter.1 hw).2 z

end GlobalTheory.LevelHecke

end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory.LevelForms

theorem finiteDimensional_of_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ (GQ L n) W) (N : ℕ), 0 < N →
    ∀ S : Submodule ℂ (GAf L n → W), (∀ f ∈ S, f ∈ NG.AFall L n ρ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) →
    FiniteDimensional ℂ S := by
  intro L _ _ _ n W _ _ _ ρ N hN S hS
  haveI := GlobalTheory.AlgFormsFin.fixedForms_finite L n ρ (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n) hN
  refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n ρ N) fun f hf => ?_
  exact ⟨(hS f hf).1.1, fun κ hκ g => congrFun ((hS f hf).2 κ hκ) g⟩

end GlobalTheory.LevelForms
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevelUnif

open GlobalTheory.LevelHecke

theorem le_exp_sub_one {x : WithZero (Multiplicative ℤ)} {n : ℤ} (h : x < WithZero.exp n) :
    x ≤ WithZero.exp (n - 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  rw [← WithZero.exp_log hx] at h ⊢
  rw [WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem T_notMem_sq (D : D7) (u : D.what₂.Word) (A : Formalism.L2.Forms.AtTTied u)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal ^ 2 := by
  set v0 := A.eV.symm ⟨v, hv⟩ with hv0
  have hU := GlobalTheory.LevelUnram.unram D u A v0
  set P := RingHom.ker (A.res v0) with hP
  haveI hPp : P.IsPrime := RingHom.ker_isPrime _
  have hvP : ∀ x, x ∈ v.asIdeal → algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P := by
    intro x hx
    have h := (A.res_v v0 x).1 (by rw [hv0, Equiv.apply_symm_apply]; exact hx)
    exact h
  have hTP : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ P := hU.1
  have hT0 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have hPbot : P ≠ ⊥ := fun h => hT0 (by rw [h] at hTP; exact (Ideal.mem_bot).1 hTP)
  have hlt : P ^ 2 < P ^ 1 := Ideal.pow_right_strictAnti P hPbot hPp.ne_top (by norm_num)
  rw [pow_one] at hlt
  obtain ⟨a, haP, ha2⟩ := SetLike.exists_of_lt hlt
  have hTE : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ P ^ 2 := by
    intro hT2
    obtain ⟨s, b, hs, hsab⟩ := hU.2 a haP
    have h1 : s * a ∈ P ^ 2 := by rw [hsab]; exact Ideal.mul_mem_right _ _ hT2
    rcases Ideal.IsPrime.mul_mem_pow P h1 with h | h
    · exact hs h
    · exact ha2 h
  intro hv2
  apply hTE
  have hle : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal ≤ P :=
    Ideal.map_le_iff_le_comap.2 (fun x hx => hvP x hx)
  have h3 := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) hv2
  rw [Ideal.map_pow] at h3
  have h4 := Ideal.pow_right_mono hle 2 h3
  simpa using h4

theorem dvd_of_val_lt_one : ∀ (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (A : Formalism.L2.Forms.AtTTied u)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (_ : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal)
    (a : v.adicCompletionIntegers D.host.F) (_ : Valued.v (a : v.adicCompletion D.host.F) < 1),
    ∃ b : v.adicCompletionIntegers D.host.F, a = (((D.mem u).A.T : ℕ) : v.adicCompletionIntegers D.host.F) * b := by
  intro D u A v hv a ha
  have hT2 := T_notMem_sq D u A v hv
  have hval : v.intValuation (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) = WithZero.exp (-1) := by
    apply le_antisymm
    · have h := (v.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hv)
      simpa using h
    · by_contra h
      push_neg at h
      have h2 := le_exp_sub_one h
      norm_num at h2
      exact hT2 ((v.intValuation_le_pow_iff_mem _ 2).1 (by simpa using h2))
  have hTv : Valued.v ((((D.mem u).A.T : ℕ) : v.adicCompletion D.host.F)) = WithZero.exp (-1) := by
    have h := v.valuedAdicCompletion_eq_valuation (K := D.host.F) (((D.mem u).A.T : ℕ) : 𝓞 D.host.F)
    rw [HeightOneSpectrum.valuation_of_algebraMap, hval] at h
    simpa using h
  have hc0 : ((((D.mem u).A.T : ℕ) : v.adicCompletion D.host.F)) ≠ 0 := by
    intro h; rw [h, map_zero] at hTv; exact WithZero.zero_ne_coe hTv
  have hale : Valued.v (a : v.adicCompletion D.host.F) ≤ WithZero.exp (-1) := by
    have h := le_exp_sub_one (n := 0) (by simpa using ha)
    simpa using h
  set c : v.adicCompletion D.host.F := (((D.mem u).A.T : ℕ) : v.adicCompletion D.host.F) with hc
  have hb : (a : v.adicCompletion D.host.F) / c ∈ v.adicCompletionIntegers D.host.F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hTv]
    rw [div_le_one₀ (by simp)]
    exact hale
  refine ⟨⟨_, hb⟩, Subtype.ext ?_⟩
  push_cast
  rw [← hc, mul_div_cancel₀ _ hc0]

end GlobalTheory.LevelUnif

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeylDimPos

theorem weylDimU_pos {p : ℕ} (lam : Fin p → ℤ) (h : ∀ i j : Fin p, i ≤ j → lam j ≤ lam i) : 0 < weylDimU lam := by
  unfold weylDimU
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
  have hij : i < j := (Finset.mem_filter.1 hj).2
  have h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
  have h2 : (0 : ℚ) ≤ ((lam i - lam j : ℤ) : ℚ) := by exact_mod_cast sub_nonneg.2 (h i j hij.le)
  exact div_pos (by linarith) (by linarith)

theorem dimK_kapW_pos {R : Ranks} (h : HCParam R) (p q : ℕ) (hpq : p + q = R.r) :
    0 < dimK p q (Formalism.L2.NTheta.kapW h p q) := by
  obtain ⟨h1, h2, -⟩ := Formalism.L2.NTheta.holOK_kapW h p q hpq
  exact mul_pos (weylDimU_pos _ fun i j hij => h1 i j hij) (weylDimU_pos _ fun i j hij => h2 i j hij)

theorem dimK_kapAt_pos {D : D7} (W : HSp D) (hW : W.SigOK) (hr : W.rank = D.R.r) (σ : D.what₂.LL →+* ℂ)
    (ρ : D.what₂.Tau) : 0 < dimK _ _ (kapAt W σ ρ) :=
  dimK_kapW_pos _ _ _ (by rw [← hr]; obtain ⟨e, -⟩ := hW (tauE D ρ); simpa using (Fintype.card_congr e).symm)

theorem dimK_kapAt_Wc_pos (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    0 < dimK _ _ (kapAt (Wc D i) σ ρ) :=
  dimK_kapAt_pos _ (D.sp.W_sig _) (D.sp.W_rank _ (by omega) (by have := i.2; omega)) σ ρ

end GlobalTheory.Mem.WeylDimPos
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TameResidue

open Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E]

theorem locK_eq_of_congr (χ : HChar E) (P : HeightOneSpectrum (𝓞 E)) (h : χ.TameAt P)
    (a b : 𝓞 E) (k l : Eˣ) (hk : (k : E) = a) (hl : (l : E) = b) (hb : b ∉ P.asIdeal)
    (hab : a - b ∈ P.asIdeal) : χ.locK P k = χ.locK P l := by
  have ha : a ∉ P.asIdeal := fun ha => hb (by simpa using P.asIdeal.sub_mem ha hab)
  have hva : P.valuation E (k : E) = 1 := by
    rw [hk]; exact (P.valuation_eq_one_iff_notMem (K := E)).2 ha
  have hvb : P.valuation E (l : E) = 1 := by
    rw [hl]; exact (P.valuation_eq_one_iff_notMem (K := E)).2 hb
  have hvd : P.valuation E ((k : E) - l) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have e : (k : E) - l = algebraMap (𝓞 E) E (a - b) := by rw [hk, hl, map_sub]
    rw [e, HeightOneSpectrum.valuation_of_algebraMap]
    exact (P.intValuation_le_pow_iff_mem (a - b) 1).2 (by simpa using hab)
  have key : χ.locK P (k * l⁻¹) = 1 := by
    refine h (atFin P (k * l⁻¹)) ?_ ?_
    · show Valued.v ((((k * l⁻¹ : Eˣ) : E)) : P.adicCompletion E) = 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Units.val_mul, Units.val_inv_eq_inv_val, map_mul,
        map_inv₀, hva, hvb]
      simp
    · have e : ((atFin P (k * l⁻¹) : (P.adicCompletion E)ˣ) : P.adicCompletion E) - 1
          = algebraMap E (P.adicCompletion E) (((k : E) - l) * (l : E)⁻¹) := by
        have e2 : ((k : E) - l) * (l : E)⁻¹ = ((k * l⁻¹ : Eˣ) : E) - 1 := by
          rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ l.ne_zero]
        rw [e2, map_sub, map_one]
        rfl
      rw [e]
      show Valued.v (((((k : E) - l) * (l : E)⁻¹ : E)) : P.adicCompletion E) ≤ _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_mul, map_inv₀, hvb]
      simpa using hvd
  rwa [map_mul, map_inv, mul_inv_eq_one] at key

theorem exists_lift (P : HeightOneSpectrum (𝓞 E)) (u : (𝓞 E ⧸ P.asIdeal)ˣ) :
    ∃ p : 𝓞 E × Eˣ, (p.2 : E) = p.1 ∧ (u : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk _ p.1 ∧ p.1 ∉ P.asIdeal := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 E ⧸ P.asIdeal)
  haveI : Nontrivial (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have hn : a ∉ P.asIdeal := fun h => u.ne_zero (by rw [← ha]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)
  have h0 : (a : E) ≠ 0 := by
    intro h
    have : a = 0 := by exact_mod_cast h
    exact hn (this ▸ P.asIdeal.zero_mem)
  exact ⟨(a, Units.mk0 (a : E) h0), rfl, ha.symm, hn⟩

theorem exists_res (χ : HChar E) (P : HeightOneSpectrum (𝓞 E)) (h : χ.TameAt P) :
    ∃ c : (𝓞 E ⧸ P.asIdeal)ˣ →* ℂˣ, ∀ (a : 𝓞 E) (k : Eˣ) (u : (𝓞 E ⧸ P.asIdeal)ˣ), (k : E) = a →
      (u : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk _ a → c u = χ.locK P k := by
  choose f hf1 hf2 hf3 using exists_lift P
  have main : ∀ (a : 𝓞 E) (k : Eˣ) (u : (𝓞 E ⧸ P.asIdeal)ˣ), (k : E) = a →
      (u : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk _ a → χ.locK P (f u).2 = χ.locK P k := by
    intro a k u hk hu
    refine (locK_eq_of_congr χ P h a (f u).1 k (f u).2 hk (hf1 u) (hf3 u) ?_).symm
    rw [← Ideal.Quotient.eq, ← hu, ← hf2 u]
  refine ⟨MonoidHom.mk' (fun u => χ.locK P (f u).2) ?_, main⟩
  intro u v
  rw [← map_mul]
  refine main ((f u).1 * (f v).1) _ _ ?_ ?_
  · rw [Units.val_mul, hf1, hf1]; simp
  · rw [Units.val_mul, map_mul, ← hf2, ← hf2]

end GlobalTheory.TameResidue

theorem GlobalTheory.exists_isRes_of_tameAt : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (P : Pl D.host.E),
    χ.TameAt P → ∃ c, IsRes χ P c :=
  fun _ χ P h => GlobalTheory.TameResidue.exists_res χ P h
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH IsDedekindDomain NumberField Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameBlockDiagonal

theorem rankV (D : D7) (k : Fin D.R.m) : (Vc D k).rank = D.R.nV := by
  rw [D.sp.V_rank _ (Nat.le_add_left _ _) k.2]

def IsBlockDiagonalWithIdentity {K : Type} [CommRing K] {n r : ℕ} (x : GL (Fin r) K) (y : GL (Fin n) K) : Prop :=
  ∀ a b : Fin n, y.val a b =
    if h : a.val < r ∧ b.val < r then x.val ⟨a.val, h.1⟩ ⟨b.val, h.2⟩ else if a = b then 1 else 0

end GlobalTheory.FrameBlockDiagonal

end
end
