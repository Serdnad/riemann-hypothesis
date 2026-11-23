module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle814
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle719
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle745
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle803
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle706
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle804
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle834
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle572
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle802
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle757
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle822
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle659
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinCompatLocalDegreeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle152
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Mathlib.RepresentationTheory.Character
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Bundle001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle827
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
public import Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle835
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem map_toDisc_eq_of_dvd {l : ℕ} {A : Type} [CommRing A] (u : A) (r : ℝ≥0) {n : Type} (k : ℕ)
    (x : Matrix n n A) (ε : Matrix n n (Disc l u r)) (hx : x.map (toDisc l u r) = ((l : ℕ) : Disc l u r) ^ k • ε)
    (h : ∀ j : n × n, ((l : ℕ) : A) ^ k ∣ x j.1 j.2) : ∃ y : Matrix n n A, y.map (toDisc l u r) = ε := by
  choose y hy using h
  refine ⟨Matrix.of fun i j => y (i, j), ?_⟩
  ext i j
  have e := congrFun (congrFun hx i) j
  have e2 : x i j = _ := hy (i, j)
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, e2, map_mul, map_pow, map_natCast] at e
  exact ((isUnit_l_disc l _ _).pow k).mul_left_cancel e

theorem IsDiscMap.map_eq_smul {l : ℕ} {A A' : Type} [CommRing A] [CommRing A'] {u : A} {u' : A'} {r r' : ℝ≥0}
    {f : A →+* A'} {F : Disc l u r →+* Disc l u' r'} (hF : IsDiscMap (l := _) (u := _) (ρ := _) f F) {n : Type} (k : ℕ)
    (x : Matrix n n A) (ε : Matrix n n (Disc l u r)) (hx : x.map (toDisc l u r) = ((l : ℕ) : Disc l u r) ^ k • ε) :
    (x.map f).map (toDisc l u' r') = ((l : ℕ) : Disc l u' r') ^ k • ε.map F := by
  ext i j
  have e := congrArg F (congrFun (congrFun hx i) j)
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast] at e ⊢
  rw [← e, hF.ext]

theorem map_mul_map_eq_smul_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (A A' : Matrix (Fin d) (Fin d) R) (e : R) (b : ℕ) (h : A * A' = e ^ b • (1 : Matrix (Fin d) (Fin d) R)) :
    A.map f * A'.map f = f e ^ b • (1 : Matrix (Fin d) (Fin d) S) := by
  rw [← Matrix.map_mul, h]
  ext i j
  simp [Matrix.one_apply, apply_ite f]

theorem Height.dvd_at_section (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (hτ : bk.IsPer τ) (hρ : ∀ g, IsUnit (ρ g)) (B : Obj l ↥(OL K)) (f f' : Hom bk.prism B)
    (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀)) (hε : ht.Rel (BK.hf f X) f f' ε) (k : ℕ)
    (x : Matrix (Fin d) (Fin d) B.A)
    (hx : x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε)
    (g : ↥(GK K)) (σ : Hom B (ainfObj K)) (h1 : σ.comp f = bk.ι) (h2 : σ.comp f' = (ainfHom K g).comp bk.ι)
    (j : Fin d × Fin d) : ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (x j.1 j.2) := by
  obtain ⟨⟨F, hF⟩, hrel⟩ := GlobalTheory.T.discPeriod_comparison_relation_map_prismHom l K bk d ρ τ s ht B (ainfObj K) f f f' bk.ι σ ε hε
  have hr := hrel F hF
  rw [h1, h2] at hr
  exact GlobalTheory.T.pow_dvd_galoisComparison_matrix l K bk d ρ τ s ht hτ hρ g (ε.map F) hr k (x.map σ.f) (hF.map_eq_smul k x ε hx) j.1 j.2

theorem matrix_phi_eq_entries {R : Type} [CommRing R] (φ : R →+* R) (e e' : R) (he : Associated e e') (d a b : ℕ)
    (P Q Q' : Matrix (Fin d) (Fin d) R) (hQ : Q * Q' = e' ^ b • (1 : Matrix (Fin d) (Fin d) R))
    (x : Matrix (Fin d) (Fin d) R) (hx : e' ^ a • (P * x.map φ) = e ^ a • (x * Q)) :
    ∃ (h : ℕ) (c : Fin d × Fin d → Fin d × Fin d → R),
      ∀ j : Fin d × Fin d, e ^ h * x j.1 j.2 = ∑ i : Fin d × Fin d, φ (x i.1 i.2) * c i j :=
  GlobalTheory.T.matrix_phi_equation_to_family_equation R R (RingHom.id R) φ e e' he d d a a b P Q Q' hQ x hx

theorem Height.exists_rel_env (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (hτ : bk.IsPer τ) (hρ : ∀ g, IsUnit (ρ g)) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) :
    ∃ ε : Matrix (Fin d) (Fin d) En.Q.A,
      ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) := by
  have tb : TopBasis (BK.hf En.inl) bk.J (Digits l) := En.tb
  have h₁ := GlobalTheory.T.comparisonMatrix_exists_on_disc l K bk d ρ τ s ht En.Q (BK.hf En.inl X) En.inl En.inr
  obtain ⟨εD, hεD⟩ := h₁
  have h₂ := GlobalTheory.T.prism_comparisonMatrix_pow_smul_bounded_on_disc l K bk d ρ τ s ht hτ En.Q En.inl En.inr _ tb εD hεD
  obtain ⟨k, x, hx⟩ := h₂
  have hφ := GlobalTheory.T.frobenius_eq_of_pow_smul_comparisonMatrix l K bk d ρ τ s ht hτ En.Q En.inl En.inr _ tb k x εD hεD hx
  have h₃ := matrix_phi_eq_entries En.Q.D.φ (BK.hf En.inl bk.E) (BK.hf En.inr bk.E)
    (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk En.Q En.inl En.inr).2.1 d (ht.a + s.N) ht.b (ht.A.map (BK.hf En.inl))
    (ht.A.map (BK.hf En.inr)) (ht.A'.map (BK.hf En.inr))
    (map_mul_map_eq_smul_one (BK.hf En.inr) _ _ _ _ ht.A_mul) x hφ
  obtain ⟨h, c, hc⟩ := h₃
  have hdiv := GlobalTheory.T.breuilKisin_envelope_frobenius_solutions_pow_dvd l K bk En (Fin d × Fin d) c h k (fun j => x j.1 j.2) hc
    (Height.dvd_at_section l K bk d ρ τ s ht hτ hρ En.Q En.inl En.inr εD hεD k x hx)
  have h₄ := map_toDisc_eq_of_dvd (BK.hf En.inl X) bk.ρ₀ k x εD hx hdiv
  obtain ⟨y, hy⟩ := h₄
  subst hy
  exact ⟨y, hεD⟩

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.MonZero

variable {l : ℕ} [hl : Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
  [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K]

theorem galOB_mul (g h : GQ l) (r : OB l O) :
    galOB O (g * h) r = galOB O g (galOB O h r) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul o w =>
    simp only [galOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact congrArg (fun z => o ⊗ₜ[ℤ_[l]] z) ((GlobalTheory.MemLoc.ActLaws.act_laws l).1 g h w)

theorem actB_mul (T : LocLat (Gl l) ℚ_[l] K O) (g h : Gl l) (x : TW (OB l O) T) :
    actB (sQ l) T (g * h) x = actB (sQ l) T g (actB (sQ l) T h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul r t =>
    have ht : T.actT (g * h) t = T.actT g (T.actT h t) :=
      Subtype.ext (show T.ρ (g * h) t = T.ρ g (T.ρ h t) by simp)
    simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_mul, galOB_mul, ht]

theorem actB_one_tmul (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (t : ↥T.L.T) :
    actB (sQ l) T g ((1 : OB l O) ⊗ₜ[O] t) = (1 : OB l O) ⊗ₜ[O] T.actT g t := by
  simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]

theorem smul_cancel (T : LocLat (Gl l) ℚ_[l] K O) (c : ℕ) {u v : TW (OB l O) T}
    (h : ((l : O) ^ c) • u = ((l : O) ^ c) • v) : u = v := by
  have e : ∀ w : TW (OB l O) T, ((l : O) ^ c) • w = ((l : OB l O) ^ c) • w := by
    intro w
    rw [← algebraMap_smul (OB l O) ((l : O) ^ c) w, map_pow, map_natCast]
  rw [e, e] at h
  exact (isUnit_l_OB.pow c).smul_left_cancel.1 h

theorem step_mul {a e : ℕ} [NeZero a] [NeZero e] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (hF : GlobalTheory.Published.FontaineBcris) (hl2 : l ≠ 2) {ι : Type} [Fintype ι] [DecidableEq ι]
    {η H : ℕ} (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T)
    (hηH : η < H) (hlH : 8 * H + 1 < l) (y : Vec K a ι) (hy : y ∈ D.Y) (hM : D.Mon y = 0) (c : ℕ)
    (hc : (l : K) ^ c • D.zeta y ∈ D.MM) (b : TW (OB l O) T) (hb : R.IsPotential y b) (g h k : Gl l)
    (hg : g = h * k) (hh : sQ l h ∈ GK (ϖ.field a)) (hk : sQ l k ∈ ϖ.GKinf) :
    ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  obtain ⟨xk, hxk⟩ := GlobalTheory.T.cocycle_mem_lattice_on_kummerTowerGalois l a e O K t ϖ ι η H D T R y hy b hb k hk
  obtain ⟨xh, hxh⟩ := GlobalTheory.T.potentialCocycle_mem_lPow_lattice l a e O K t ϖ ι η H D T R hηH hlH y hy c hc b hb h hh
    (GlobalTheory.T.galois_coboundary_mem_lattice_inv_l_of_monodromy_eq_zero hF l a e O K t ϖ hl2 ι η H D T R y hy hM b hb h hh)
  refine ⟨(l : O) ^ c • T.actT h xk + xh, ?_⟩
  have e1 : actB (sQ l) T g b - b = actB (sQ l) T h (actB (sQ l) T k b - b) + (actB (sQ l) T h b - b) := by
    rw [hg, actB_mul, map_sub]; abel
  rw [e1, hxk, actB_one_tmul, smul_add, hxh, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_add]

theorem cob_of (T : LocLat (Gl l) ℚ_[l] K O) (b : TW (OB l O) T) (c : ℕ) (X : Gl l → ↥T.L.T)
    (hX : ∀ g, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] X g) :
    IsCobOf (sQ l) T b (fun g => ((l : K) ^ c)⁻¹ • (X g : T.V)) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hne : (l : K) ^ c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  intro g n x hx
  apply smul_cancel T c
  rw [smul_comm ((l : O) ^ c) ((l : O) ^ n), hX g, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_smul]
  rw [← algebraMap_smul K ((l : O) ^ c), ← algebraMap_smul K ((l : O) ^ n), map_pow, map_pow, map_natCast, hx,
    smul_comm ((l : K) ^ n), smul_smul ((l : K) ^ c), mul_inv_cancel₀ hne, one_smul]

theorem exists_cob {a e : ℕ} [NeZero a] [NeZero e] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (hF : GlobalTheory.Published.FontaineBcris) (hl2 : l ≠ 2) {ι : Type} [Fintype ι] [DecidableEq ι]
    {η H : ℕ} (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T)
    (hηH : η < H) (hlH : 8 * H + 1 < l) (y : Vec K a ι) (hy : y ∈ D.Y) (hM : D.Mon y = 0) (c : ℕ)
    (hc : (l : K) ^ c • D.zeta y ∈ D.MM) (b : TW (OB l O) T) (hb : R.IsPotential y b)
    (hdec : ∀ g : Gl l, ∃ h k : Gl l, g = h * k ∧ sQ l h ∈ GK (ϖ.field a) ∧ sQ l k ∈ ϖ.GKinf) :
    ∃ κ : Gl l → T.V, IsCobOf (sQ l) T b κ ∧ ∀ g, (l : K) ^ c • κ g ∈ T.L.T := by
  have hX : ∀ g : Gl l, ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
    intro g
    obtain ⟨h, k, hg, hh, hk⟩ := hdec g
    exact step_mul t ϖ hF hl2 D T R hηH hlH y hy hM c hc b hb g h k hg hh hk
  choose X hX using hX
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hne : (l : K) ^ c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  refine ⟨_, cob_of T b c X hX, fun g => ?_⟩
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  exact (X g).2

end GlobalTheory.BKGal.MonZero

theorem GlobalTheory.BKGal.classOf_of_mon_eq_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat ↥(OL LL) ↥LL.1 l e a ι η H) (T : QLat LL) (R : GalDat (thetaW a LL) ϖ (sQ l) D T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, D.Mon y = 0 → ∀ c : ℕ, (l : ↥LL.1) ^ c • D.zeta y ∈ D.MM → ∃ κ₁ ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, R.ClassOf ((l : ↥LL.1) ^ c • y) κ₁ := by
  intro hF l _ a e _ _ ϖ LL _ _ ι _ _ η H D T R Pl AI hstd hηH hlH y hy hM c hc
  have hl2 : l ≠ 2 := by omega
  obtain ⟨b, hb⟩ := (GlobalTheory.T.exists_frobeniusPotential_cocycle_class l a e _ _ (thetaW a LL) ϖ ι η H D T R).1 y hy
  have hdec : ∀ g : Gl l, ∃ h k : Gl l, g = h * k ∧ sQ l h ∈ GK (ϖ.field a) ∧ sQ l k ∈ ϖ.GKinf := by
    intro g
    obtain ⟨h, hh, k, hk, hgk⟩ := (GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL).1 (sQ l g)
    let hG : Gl l := ⟨h, GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := ϖ.field a) bot_le hh⟩
    refine ⟨hG, hG⁻¹ * g, (mul_inv_cancel_left hG g).symm, hh, ?_⟩
    have e1 : sQ l (hG⁻¹ * g) = k := by
      rw [map_mul, map_inv, show sQ l g = h * k from hgk]
      show h⁻¹ * (h * k) = k
      group
    rw [e1]; exact hk
  obtain ⟨κ, hcob, hT⟩ := GlobalTheory.BKGal.MonZero.exists_cob (thetaW a LL) ϖ hF hl2 D T R hηH hlH y hy hM c hc b hb hdec
  have hcl : R.ClassOf y κ := ⟨b, hb, hcob⟩
  have hZ1c : κ ∈ continuousCocycles T.ρ := GlobalTheory.T.coboundary_mem_cocycles_odd_prime l hl2 LL T b κ hcob
  obtain ⟨β, -, -, -, hf⟩ := GlobalTheory.T.exists_bcrisTensorLattice_equiv_periodRing l LL T Pl AI hstd
  have hZ1f : κ ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ := (hf κ hZ1c).2 ⟨b, hcob⟩
  refine ⟨(l : ↥LL.1) ^ c • κ, ?_, (GlobalTheory.T.exists_frobeniusPotential_cocycle_class l a e _ _ (thetaW a LL) ϖ ι η H D T R).2.2.1 y κ c hcl⟩
  refine ⟨⟨(continuousCocycles T.ρ).smul_mem _ hZ1c, ?_⟩, (finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ).smul_mem _ hZ1f⟩
  intro g _
  exact hT g
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.JumpsOfM

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  intro hF l _ a e _ _ ϖ LL _ hT hl ι _ _ P T I jB Pl AI hStd hCmp hHor hEN U hU i hi
  obtain ⟨x, hfix, hx, hx'⟩ := GlobalTheory.T.exists_fixed_vector_filtration_jump_breuilKisin hF l a e ϖ LL hl ι P T I jB Pl AI hStd hCmp hHor hEN i hi
  have hdvd : e ∣ l ^ a - 1 := ⟨1, by rw [← hT.succ_eq]; simp⟩
  have hG := PiSys.isGalois_field a ϖ hdvd
  let τ : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] ↥LL.1 :=
    (Algebra.ofId ℚ_[l] ↥LL.1).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toAlgHom
  exact hU τ i (GlobalTheory.T.isHodgeTateJump_of_galois_fixed_filtration_vector l Pl LL T (ϖ.field a) hG i x hfix hx hx' τ)

end GlobalTheory.JumpsOfM
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isStratifiedPhiModuleHom_of_galois_equivariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → IsStratHom S S' Y := by
  first | exact @GlobalTheory.isStratHom_of_equivariant | exact GlobalTheory.isStratHom_of_equivariant | (intros; apply GlobalTheory.isStratHom_of_equivariant <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isLanglandsData_transport_localFieldIso : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (l : List (Segment k)) (l' : List (Segment k')) (x : IrrGL (k := k)) (x' : IrrGL (k := k')), List.Forall₂ (fun (Δ : Segment k) (Δ' : Segment k') => RepRel i Δ.first Δ'.first ∧ Δ.len = Δ'.len) l l' → RepRel i x x' → IsL (l : Multiset (Segment k)) x.rep → IsL (l' : Multiset (Segment k')) x'.rep := by
  first | exact @GlobalTheory.LocLanglands.isL_transport | exact GlobalTheory.LocLanglands.isL_transport | (intros; apply GlobalTheory.LocLanglands.isL_transport <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.globalArtin_compat_localDegreeOne : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∀ (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (art' : Neutral.B1.Ideles E' →* GlobalTheory.HeckeGal.Gab E' Ω'), GlobalTheory.HeckeGal.IsGlobalArtin art → GlobalTheory.HeckeGal.IsGlobalArtin art' → ∀ (σ : Weil h) (σ' : Weil h') (x : (w.adicCompletion E)ˣ), WeilRel φ σ σ' → art' (Neutral.B1.localIdele E' w' (Units.map i.toRingHom.toMonoidHom x)) = GlobalTheory.HeckeGal.toAb E' Ω' σ' → art (Neutral.B1.localIdele E w x) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  first | exact @GlobalTheory.LocDegOne.artin_of_placeIso | exact GlobalTheory.LocDegOne.artin_of_placeIso | (intros; apply GlobalTheory.LocDegOne.artin_of_placeIso <;> assumption)
end

section

open GlobalTheory.MeetsGen CategoryTheory

noncomputable section

namespace GlobalTheory.MeetsUnit

variable {G : Type} [Group G] [Fintype G]

theorem single_mul_cU (U : Subgroup G) [Fintype U] (f : U → ℂ) (h : G) :
    MonoidAlgebra.single h (1 : ℂ) * cU U f = cU U f * MonoidAlgebra.single h 1 := by
  unfold cU
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
  have e1 : MonoidAlgebra.single (h * g) (1 : ℂ) = MonoidAlgebra.single h 1 * MonoidAlgebra.single g 1 := by
    rw [MonoidAlgebra.single_mul_single, one_mul]
  have e2 : MonoidAlgebra.single (h * g)⁻¹ (1 : ℂ) * MonoidAlgebra.single h 1 = MonoidAlgebra.single g⁻¹ 1 := by
    rw [MonoidAlgebra.single_mul_single, one_mul, mul_inv_rev, inv_mul_cancel_right]
  simp only [Equiv.coe_mulLeft]
  rw [mul_assoc _ (MonoidAlgebra.single (h * g)⁻¹ (1 : ℂ)), e2, e1]
  simp only [mul_assoc]

theorem single_mul_uElt (U : Subgroup G) [Fintype U] (f : U → ℂ) (e : MonoidAlgebra ℂ G)
    (hC : ∀ a, e * a = a * e) (h : G) :
    MonoidAlgebra.single h (1 : ℂ) * uElt U f e = uElt U f e * MonoidAlgebra.single h 1 := by
  have hc := single_mul_cU U f h
  have he := hC (MonoidAlgebra.single h 1)
  simp only [uElt, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul]
  rw [he, mul_assoc (cU U f) e, he, ← mul_assoc, ← mul_assoc, hc]

theorem trace_cU (V : FDRep ℂ G) (U : Subgroup G) [Fintype U] (f : U → ℂ) :
    LinearMap.trace ℂ V (Representation.asAlgebraHom V.ρ (cU U f)) =
      (Fintype.card G : ℂ) * ∑ u : U, ((Fintype.card U : ℂ)⁻¹ * f u) * V.character u := by
  have hp : Representation.asAlgebraHom V.ρ (pU U f) = ∑ u : U, ((Fintype.card U : ℂ)⁻¹ * f u) • V.ρ u := by

    simp only [pU, map_sum, Representation.asAlgebraHom_single]
  unfold cU

  rw [map_sum, map_sum]
  rw [Finset.sum_congr rfl (fun g _ => by
    rw [map_mul (Representation.asAlgebraHom V.ρ), map_mul (Representation.asAlgebraHom V.ρ), Representation.asAlgebraHom_single, Representation.asAlgebraHom_single, one_smul,
      one_smul, LinearMap.trace_mul_comm ℂ, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul])]

  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hp, map_sum]
  simp only [map_smul, smul_eq_mul, FDRep.character]

def lreg : Representation ℂ G (MonoidAlgebra ℂ G) :=
  (Algebra.lmul ℂ (MonoidAlgebra ℂ G)).toRingHom.toMonoidHom.comp (MonoidAlgebra.of ℂ G)

theorem lreg_apply (g : G) (x : MonoidAlgebra ℂ G) : lreg g x = MonoidAlgebra.single g 1 * x := rfl

theorem exists_rightInv_uElt : ∀ {G : Type} [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (ψ : U →* ℂˣ)
    (e : MonoidAlgebra ℂ G), e * e = e → (∀ a, e * a = a * e) →
    (∀ χ : G → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, e.coeff g * χ g = χ 1 →
      ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0) →
    ∃ v : MonoidAlgebra ℂ G, uElt U (fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ)) e * v = 1 := by
  intro G _ _ U _ ψ e hI hC hχ
  classical
  set f : U → ℂ := fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ) with hf
  set w := uElt U f e with hw
  have hinj : Function.Injective (LinearMap.mulLeft ℂ w) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    by_contra hy0
    let K : Submodule ℂ (MonoidAlgebra ℂ G) := LinearMap.ker (LinearMap.mulLeft ℂ w)
    have hK : ∀ x, x ∈ K ↔ w * x = 0 := fun x => LinearMap.mem_ker
    let A : Subrepresentation (lreg (G := G)) := ⟨K, fun g x hx => by
      rw [hK] at hx ⊢
      rw [lreg_apply, ← mul_assoc, ← single_mul_uElt U f e hC g, mul_assoc, hx, mul_zero]⟩
    haveI : Nontrivial A.toSubmodule :=
      Submodule.nontrivial_iff_ne_bot.2 (fun hb => hy0 ((Submodule.eq_bot_iff _).1 hb y hy))
    obtain ⟨τ, hτs, φ, hφ, hφ0⟩ := PI.GreenLabelSurjWork.exists_simple_constituent A.toRepresentation
    haveI := hτs
    haveI := PI.CharIdemW.nontrivial_of_simple τ
    have hcomm : ∀ a : MonoidAlgebra ℂ G, (∀ k : G, MonoidAlgebra.single k (1 : ℂ) * a = a * MonoidAlgebra.single k 1) →
        ∀ k : G, τ.ρ k * Representation.asAlgebraHom τ.ρ a = Representation.asAlgebraHom τ.ρ a * τ.ρ k := by
      intro a ha k
      rw [← Representation.asAlgebraHom_single_one, ← map_mul, ← map_mul, ha k]
    obtain ⟨μ, hμ⟩ := PI.CharIdemW.schur_scalar τ _ (hcomm w (single_mul_uElt U f e hC))
    obtain ⟨ν, hν⟩ := PI.CharIdemW.schur_scalar τ _ (hcomm e (fun k => hC _ |>.symm))
    have hφw : ∀ x, φ (Representation.asAlgebraHom τ.ρ w x) = 0 := by
      intro x

      rw [GlobalTheory.GoodFactor.asAlg_eq τ.ρ w, LinearMap.sum_apply, map_sum]
      simp only [LinearMap.smul_apply, map_smul]
      have h1 : ∀ g, φ (τ.ρ g x) = A.toRepresentation g (φ x) := fun g => LinearMap.congr_fun (hφ g) x
      simp only [h1]
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      show ∑ g, w.coeff g • (MonoidAlgebra.single g (1 : ℂ) * (φ x : MonoidAlgebra ℂ G)) = 0
      have h2 : ∀ g, w.coeff g • (MonoidAlgebra.single g (1 : ℂ) * (φ x : MonoidAlgebra ℂ G)) =
          MonoidAlgebra.single g (w.coeff g) * (φ x : MonoidAlgebra ℂ G) := fun g => by
        rw [← smul_mul_assoc, MonoidAlgebra.smul_single', mul_one]
      simp only [h2]
      rw [← Finset.sum_mul, GlobalTheory.GoodFactor.sum_single]
      exact (hK _).1 (φ x).2
    have hμ0 : μ = 0 := by
      by_contra h
      apply hφ0
      refine LinearMap.ext fun x => ?_
      have h3 : x = μ⁻¹ • Representation.asAlgebraHom τ.ρ w x := by
        rw [hμ, LinearMap.smul_apply, Module.End.one_apply, smul_smul, inv_mul_cancel₀ h, one_smul]
      rw [h3, map_smul, hφw, smul_zero, LinearMap.zero_apply]
    have h10 : (1 : Module.End ℂ τ) ≠ 0 := one_ne_zero
    have hνν : ν * ν = ν := by
      have h4 : Representation.asAlgebraHom τ.ρ (e * e) = Representation.asAlgebraHom τ.ρ e := by rw [hI]
      rw [map_mul, hν, smul_mul_smul_comm, one_mul] at h4
      exact smul_left_injective ℂ h10 h4
    have hTw : Representation.asAlgebraHom τ.ρ w =
        Representation.asAlgebraHom τ.ρ (cU U f) * Representation.asAlgebraHom τ.ρ e + 1 -
          Representation.asAlgebraHom τ.ρ e := by
      rw [hw, uElt, map_add (f := _), map_mul, map_sub, map_one, add_sub_assoc]
    rw [hμ, hμ0, zero_smul, hν] at hTw
    have hν01 : ν * (ν - 1) = 0 := by linear_combination hνν
    rcases mul_eq_zero.mp hν01 with h0 | h0
    · rw [h0, zero_smul, mul_zero, zero_add, sub_zero] at hTw
      exact h10 hTw.symm
    · have hν1 : ν = 1 := sub_eq_zero.mp h0
      rw [hν1, one_smul, mul_one, add_sub_cancel_right] at hTw
      have htr := trace_cU τ U f
      rw [← hTw, map_zero] at htr
      have hirr := GlobalTheory.GoodFactor.isIrrChar_character τ hτs
      have hfix : ∑ g, e.coeff g * τ.character g = τ.character 1 := by
        have h5 : LinearMap.trace ℂ τ (Representation.asAlgebraHom τ.ρ e) = ∑ g, e.coeff g * τ.character g := by

          rw [GlobalTheory.GoodFactor.asAlg_eq τ.ρ e, map_sum]
          simp only [map_smul, smul_eq_mul, FDRep.character]
        rw [← h5, hν, hν1, one_smul, FDRep.character, map_one τ.ρ]
      have hne := hχ _ hirr hfix
      have h6 : ∑ u : U, ((Fintype.card U : ℂ)⁻¹ * f u) * τ.character u =
          (Fintype.card U : ℂ)⁻¹ * ∑ u : U, τ.character u * f u := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by ring
      rw [h6] at htr
      have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have hU : (Fintype.card U : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      exact mul_ne_zero hG (mul_ne_zero hU hne) htr.symm
  obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.1 hinj 1
  exact ⟨v, hv⟩

end GlobalTheory.MeetsUnit
end
end

section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.card_localMatrixDivisionPointQuotient : ∀ (E : Type) [Field E] [NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (N m n : ℕ), 0 < N → Nat.card (GlobalTheory.DivPtLocal.LocQ w N m n) = Nat.card (w.adicCompletionIntegers E ⧸ Ideal.span {((N : ℕ) : w.adicCompletionIntegers E)}) ^ (m * n) := by
  first | exact @GlobalTheory.DivPtLocal.Count.card_locQ | exact GlobalTheory.DivPtLocal.Count.card_locQ | (intros; apply GlobalTheory.DivPtLocal.Count.card_locQ <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.DIV Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rationalHecke_read_as_cosetSums : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Formalism.L2.Pj.CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, Formalism.IndefR.FWT.JEvAt T R κ v₀ i (sg0 D A) hV) → Function.Injective ((R.FW i).j (sg0 D A)) → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, GlobalTheory.HeckeSup.ReadsCusp T R κ i (Formalism.IndefR.FWT.res T (sg0 D A)) hV) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R i := by
  first | exact @GlobalTheory.HeckeReadRational.rationalHecke_of_readsCusp | exact GlobalTheory.HeckeReadRational.rationalHecke_of_readsCusp | (intros; apply GlobalTheory.HeckeReadRational.rationalHecke_of_readsCusp <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

theorem _root_.GlobalTheory.T.lengthBound_of_rowConditions_and_dualityTheorems : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.AllDesignConditions D → TruncatedSeriesCountingIdentities.Stmt D := by
  first | exact @GlobalTheory.InertiaEigenvalues.LengthBoundClosing.stmt_closed | exact GlobalTheory.InertiaEigenvalues.LengthBoundClosing.stmt_closed | (intros; apply GlobalTheory.InertiaEigenvalues.LengthBoundClosing.stmt_closed <;> assumption)
end
