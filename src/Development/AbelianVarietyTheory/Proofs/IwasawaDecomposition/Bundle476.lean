module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle027
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle137
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFlagBasisVectorEqSingleOfNoExtra
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle131
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.Columns.Bundle011
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.Bundle001
public import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT


open Classical GlobalTheory.TopStep in
theorem sub_mem_stdAt_of_redV {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
    (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (m : GLint E n P) (x : Sp E n)
    (hx : (qOf P : E) • x ∈ stdAt E n P) (hred : ∀ v ∈ stdAt E n P, redV P (m.1 v) = redV P v) :
    m.1 x - x ∈ stdAt E n P := by
  have hq0 : (qOf P : E) ≠ 0 := qOf_ne_zero
  have hk0 := glint_mem m hx
  refine mem_stdAt.2 fun j => ?_
  have hi1 := mem_stdAt.1 hk0 j
  have hi2 := mem_stdAt.1 hx j
  have hr : redP P ((m.1 ((qOf P : E) • x) - (qOf P : E) • x) j) = 0 := by
    rw [Pi.sub_apply, reduction_sub hi1 hi2, sub_eq_zero]
    exact congrFun (hred _ hx) j
  have := intAt_div_of_redP hq (intAt_sub hi1 hi2) hr
  convert this using 1
  rw [LinearEquiv.map_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp



open Classical GlobalTheory.TopStep in
theorem cosetIn_act_of_liftsInv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (p : (I.stp u a i).D b) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), (I.stp u a i).gam b κ = 1 → LiftsInv I κ P g → ∀ z, z ∈ cosetIn ((I.stp u a i).act b κ p) P ↔ g z ∈ cosetIn p P := by
  intro B X I _ u a i b κ p P g hgam hL z
  have hX : B.fields.Ok := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hPr : (B.primes X).Ok := (GlobalTheory.BasePrimes.primes_ok B X).1
  obtain ⟨γ, h, c⟩ := κ
  have hγ : γ = 1 := by
    have e : ufGL B.fields.E (B.R.N i) γ = 1 := hgam
    have e2 : (toGLm B.fields.E (B.R.N i)) γ.1 = (toGLm B.fields.E (B.R.N i)) 1 := by
      rw [map_one]; exact e
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective e2)
  subst hγ
  set p' := (I.stp u a i).act b ((1 : UF B.fields.E (B.R.N i)), h, c) p with hp'
  have hys : p'.1.2 = p.1.2 := by
    show (fun v => ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) v) '' p.1.2 = p.1.2
    simp
  have hg : ∀ x, g x ∈ stdAt B.fields.E (B.R.N i) P.1 ↔ x ∈ stdAt B.fields.E (B.R.N i) P.1 := hL.1
  have key : ∀ y ∈ p.1.2, ((qOf P.1 : B.fields.E) ^ (if P.1 ∈ (B.primes X).vGs then 0 else (I.cst a).M))⁻¹ •
      (g ((frsF I.sel (I.tup a) p'.1.1 P).symm y) - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈ stdAt B.fields.E (B.R.N i) P.1 := by
    intro y hy
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · rw [if_pos hP, pow_zero, inv_one, one_smul]
      by_cases hj : i + 1 = B.R.m
      swap
      · have h0 : p.1.2 = ∅ := by
          have := p.2
          rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj] at this
          exact this
        rw [h0] at hy
        exact absurd hy (Set.notMem_empty y)
      obtain ⟨y0, hy0, hY⟩ := PtAt.mem_ybSet p hj
      have hy' : y - y0 ∈ locLat (rowSG (B.primes X) I.sel (I.tup a)) p.1.1.deco.1.N
          (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst a).M : ℤ)) := by
        rw [hY] at hy
        exact hy
      have hA : (qOf P.1 : B.fields.E) • y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy0 P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hB : y - y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy' P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hx : (qOf P.1 : B.fields.E) • y ∈ p.1.1.deco.1.at P.1 := by
        have e : (qOf P.1 : B.fields.E) • y = (qOf P.1 : B.fields.E) • y0 + (qOf P.1 : B.fields.E) • (y - y0) := by
          rw [← smul_add, add_sub_cancel]
        rw [e]
        exact add_mem hA (smul_mem_locP (intAt_nat _) hB)
      let w : (B.primes X).vGs := ⟨P.1, hP⟩
      have hd : p'.1.1.deco.1 = p.1.1.deco.1.act ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) h.1 := rfl
      have hf : IsLiftFr p.1.1.deco.1 w (p.1.1.deco.1.liftFr w) := liftFr_spec p.1.1.deco.2 w
      have hf' : IsLiftFr (p.1.1.deco.1.act ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) h.1) w (p'.1.1.deco.1.liftFr w) := by
        rw [← hd]
        exact liftFr_spec p'.1.1.deco.2 w
      have e1 : frsF I.sel (I.tup a) p.1.1 P = p.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dite_eq_left hP]
      have e2 : frsF I.sel (I.tup a) p'.1.1 P = p'.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dite_eq_left hP]
      rw [e1, e2]
      have e3 : (p'.1.1.deco.1.liftFr w).symm y = (passFr (w := w) _ h.1 hf hf').1 ((p.1.1.deco.1.liftFr w).symm y) := by
        show _ = (p'.1.1.deco.1.liftFr w).symm (((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) ((p.1.1.deco.1.liftFr w) ((p.1.1.deco.1.liftFr w).symm y)))
        rw [LinearEquiv.apply_symm_apply]
        rfl
      rw [e3]
      have hv0 : (qOf P.1 : B.fields.E) • (p.1.1.deco.1.liftFr w).symm y ∈ stdAt B.fields.E (B.R.N i) P.1 := by
        rw [← LinearEquiv.map_smul, ← hf.1, LinearEquiv.apply_symm_apply]
        exact hx
      have hκ : GlobalTheory.TopStep.redGL (B.R.N i) P.1 (passFr (w := w) _ h.1 hf hf') = h.1 w := redGL_passFr (w := w) _ h.1 hf hf'
      have hq := (degOneUnram_of_mem_vGs hX hPr hP).2
      have hred : ∀ v ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (g ((passFr (w := w) _ h.1 hf hf').1 v)) = redV P.1 v := by
        intro v hv
        rw [hL.2.1 hP _ (glint_mem _ hv), redV_redGL _ hv, hκ, Matrix.mulVec_mulVec]
        show ((h.1 w)⁻¹.1 * (h.1 w).1).mulVec _ = _
        rw [Units.inv_mul, Matrix.one_mulVec]
      have hm := sub_mem_stdAt_of_redV P.1 hq (⟨g, hL.1⟩ * passFr (w := w) _ h.1 hf hf') _ hv0 hred
      exact hm
    · rw [if_neg hP]
      have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
      have hF' : frsF I.sel (I.tup a) p'.1.1 P = frsF I.sel (I.tup a) p.1.1 P * g := by
        unfold frsF
        rw [dite_eq_right hP, dite_eq_right hP, hL.2.2 hQ]
        exact LinearEquiv.ext fun x => rfl
      have e : g ((frsF I.sel (I.tup a) p'.1.1 P).symm y) = (frsF I.sel (I.tup a) p.1.1 P).symm y := by
        rw [eq_comm, LinearEquiv.symm_apply_eq]
        rw [hF']
        exact ((frsF I.sel (I.tup a) p.1.1 P * g).apply_symm_apply y).symm
      rw [e, sub_self, smul_zero]
      exact zero_mem _
  simp only [cosetIn, Set.mem_ofPred_eq]
  rw [hys]
  constructor
  · rintro ⟨y, hy, hz⟩
    refine ⟨y, hy, ?_⟩
    have := add_mem ((hg _).2 hz) (key y hy)
    rwa [map_smul, map_sub, ← smul_add, sub_add_sub_cancel] at this
  · rintro ⟨y, hy, hz⟩
    refine ⟨y, hy, ?_⟩
    have := sub_mem hz (key y hy)
    rw [← smul_sub, sub_sub_sub_cancel_right, ← map_sub, ← map_smul] at this
    exact (hg _).1 this

end GlobalTheory.Mem.Col2.AdT

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep

section Local

variable {E : Type} [Field E] {N : ℕ}

theorem prXpG_sumE (hN : N = (N - 1) + 1) (g : Sp E (N - 1) ≃ₗ[E] Sp E (N - 1)) :
    prXpG E N ∘ₗ (sumE hN g 1).toLinearMap = (g.toLinearMap : Sp E ((N - 1) + 0) →ₗ[E] Sp E ((N - 1) + 0)) ∘ₗ prXpG E N := by
  refine LinearMap.ext fun x => funext fun i => ?_

  exact congrFun (prH_sumE hN g 1 x) i

theorem atNL_sumE (hN : N = (N - 1) + 1) (g : Sp E (N - 1) ≃ₗ[E] Sp E (N - 1)) :
    atNL E N (N - 1) ∘ₗ (sumE hN g 1).toLinearMap = atNL E N (N - 1) := by
  refine LinearMap.ext fun x => ?_
  have hlt : N - 1 < N := by omega

  have h := sumE_last hN g 1 x
  rw [Units.val_one, one_mul] at h
  simp only [LinearMap.comp_apply, atNL, dif_pos hlt, LinearMap.proj_apply]
  exact h

end Local

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep

theorem exists_topLev_liftsInv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m →
    ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (P : SBof I a), ∃ g g' z,
      GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P g z ∧ LiftsInv I κ P g' ∧
        CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) g g' := by
  intro B X I hI u a i hi b κ P
  subst hi

  rcases b with ⟨_ | b₀, hb⟩
  swap
  · exact absurd (hb.mp rfl) (lt_irrefl _)
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1

  have hq : ((qOf P.1 : ℕ) : 𝓞 B.fields.E) ∉ P.1.asIdeal ^ 2 :=
    Formalism.L2.Ker.mq_rowSG_unif (I.tup a) (GlobalTheory.Mem.FieldsLaws.fields_ok (B := B)) hPr hI.sel_ok P
  have hN := N_m_succ B.R
  by_cases hP : P.1 ∈ (B.primes X).vGs
  ·
    have hQn : P.1 ∉ I.Q a := QE_disj (I.tup a) hPr hI.sel_ok hI.g_mem P.1 hP
    have hmem : κ.2.1.1 ⟨P.1, hP⟩ ∈ (levGTop I.Ch I.Ps ⟨P.1, hP⟩).H := by
      have h := κ.2.1.2
      simp only [LevFam.grp, Subgroup.mem_pi] at h
      rw [← topLev_levG_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps]
      exact h ⟨P.1, hP⟩ (Set.mem_univ _)
    obtain ⟨h₀, hh₀, hdiag⟩ := (mem_levDiag _ _ _).mp hmem
    rw [rowTyG_PsymF_H] at hh₀
    have hr : B.R.r = B.R.k + 2 * B.R.rS + 1 := by
      simp only [Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r]
      obtain ⟨s, hs⟩ := B.R.m_even
      have := B.R.two_le_m
      omega
    have hsym : rSym B.R.k B.R.rS = B.R.r := by rw [hr]; rfl

    have hJ := (mem_HJsym_iff_JSymG (𝓞 B.fields.E ⧸ P.1.asIdeal) (B.R.N B.R.m - 1) B.R.k B.R.r B.R.t B.R.m B.R.rS
      (r_le_X' B.R) hr B.R.t_odd.pos (rank_X'_eq B.R) h₀⁻¹).mp (Subgroup.inv_mem _ hh₀)

    obtain ⟨j, hj⟩ := redGL_surjective (E := B.fields.E) (n := B.R.N B.R.m - 1) P.1 h₀⁻¹
    have hjinv : redGL _ P.1 j⁻¹ = h₀ := by rw [map_inv, hj, inv_inv]
    have hlev : j.1 ∈ GlobalTheory.TwU.rowLevTop (B.primes X) B.R (I.cst a).sharp (B.R.N B.R.m) P.1 := by
      have h := GlobalTheory.Mem.LastGrp.mem_JGsym0 (fun x hx h0 => intAt_div_of_redP hq hx h0)
        (hsym.symm ▸ r_le_X' B.R) j
        (fun x y hxy => by rw [← redGL_val, hj]; exact hJ.1.1 x y hxy)
        (fun x y hxy => by rw [← redGL_val, hjinv]; simpa using hJ.2.1 x y hxy)
        (fun x hx => by rw [← redGL_val, hj]; exact hJ.1.2.1 x hx)
        (fun x y hx hy => by rw [← redGL_val, hj]; exact hJ.1.2.2.1 x y hx hy)
      have e : GlobalTheory.CongLevel.extE 0 j.1 = j.1 := LinearEquiv.ext (GlobalTheory.Mem.LastGrp.extE_zero j.1)
      rw [e, hsym] at h
      simp only [GlobalTheory.TwU.rowLevTop, if_pos hP, hI.sharp a, if_true]
      exact h
    refine ⟨sumE hN j.1 1, sumE hN j.1 1, _, ⟨j.1, hlev, prXpG_sumE hN j.1, atNL_sumE hN j.1, rfl⟩, ⟨?_, ?_, ?_⟩, congE_refl _ _ _⟩
    · rw [← extI_val hN j]
      exact (extI hN P.1 j).2
    · intro h x hx
      rw [← extI_val hN j, redV_redGL _ hx, redGL_extI, hj, ← hdiag, ← map_inv]
    · exact fun h => absurd h hQn
  ·
    have hQ : P.1 ∈ I.Q a := by
      classical
      have h := P.2
      simp only [SBof, rowSG, uSG, Finset.mem_union] at h
      exact h.resolve_left hP
    have hmem : κ.2.2.1 ⟨P.1, hQ⟩ ∈ (levQTop B.R I.sel (I.tup a) (topDep B.R (I.cst a).M) ⟨P.1, hQ⟩).H := by
      have h := κ.2.2.2
      simp only [LevQFam.grp, Subgroup.mem_pi] at h
      rw [← topLev_levQ_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps]
      exact h ⟨P.1, hQ⟩ (Set.mem_univ _)
    simp only [levQTop] at hmem
    obtain ⟨j, hj, hjc⟩ := (mem_levCong _ _ _ _).mp (Subgroup.inv_mem _ hmem)
    have hlev : j.1 ∈ GlobalTheory.TwU.rowLevTop (B.primes X) B.R (I.cst a).sharp (B.R.N B.R.m) P.1 := by
      simp only [GlobalTheory.TwU.rowLevTop, if_neg hP]
      exact GlobalTheory.TopLaw.mem_JQ_of_red hq j ((mem_levRed _ _).mp hj)
    refine ⟨sumE hN j.1 1, ((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹).1, _, ⟨j.1, hlev, prXpG_sumE hN j.1, atNL_sumE hN j.1, rfl⟩,
      ⟨((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹).2, fun h => absurd h hP, fun h => rfl⟩, ?_⟩

    have h2 : (extI hN P.1 j)⁻¹ * (κ.2.2.1 ⟨P.1, hQ⟩)⁻¹ ∈ prinCong _ P.1 (2 * (I.cst a).M) :=
      prinCong_anti (by have := two_mul_le_topDep B.R (I.cst a).M; omega) hjc
    have h3 : ((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹)⁻¹ * extI hN P.1 j ∈ prinCong _ P.1 (2 * (I.cst a).M) := by
      have := Subgroup.inv_mem _ h2
      rwa [_root_.mul_inv_rev, inv_inv] at this
    have h4 := (inv_mul_mem_prinCong _ _ _).mp h3
    intro x hx
    simp only [GlobalTheory.TwU.topDep, if_neg hP]
    have := h4 x hx
    rwa [extI_val] at this

end GlobalTheory.Mem.Col2.AdT
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary

theorem vAlg {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x

theorem v_qOf {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (hp : (qOf P).Prime)
    (h2 : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
  have e : ((qOf P : ℕ) : P.adicCompletion E) = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E ((qOf P : ℕ) : 𝓞 E)) := by
    simp
  rw [e, vAlg, HeightOneSpectrum.valuation_of_algebraMap]
  have hmem : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal ^ 1 := by
    rw [pow_one]
    exact Ideal.absNorm_mem P.asIdeal
  have h1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem P _ 1).2 hmem
  have h2' : ¬ P.intValuation ((qOf P : ℕ) : 𝓞 E) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h =>
    h2 ((HeightOneSpectrum.intValuation_le_pow_iff_mem P _ 2).1 h)
  have hne : P.intValuation ((qOf P : ℕ) : 𝓞 E) ≠ 0 := by
    have : ((qOf P : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    exact (HeightOneSpectrum.intValuation_ne_zero P _ this)
  rw [← WithZero.exp_log hne] at h1 h2' ⊢
  rw [WithZero.exp_le_exp] at h1 h2'
  congr 1
  push_cast at h1 h2'
  omega

theorem exists_clear {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (y : FiniteAdeleRing (𝓞 E) E)
    (hP : Valued.v (y P) ≤ 1) : ∃ s : 𝓞 E, s ∉ P.asIdeal ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) * y Q) ≤ 1 := by
  have hfin : {Q : HeightOneSpectrum (𝓞 E) | ¬ y Q ∈ Q.adicCompletionIntegers E}.Finite :=
    Filter.eventually_cofinite.1 y.2
  set S := hfin.toFinset with hS
  have memS : ∀ Q, Q ∈ S ↔ 1 < Valued.v (y Q) := by
    intro Q
    rw [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq, HeightOneSpectrum.mem_adicCompletionIntegers, not_le]
  have hPS : P ∉ S := fun h => absurd hP (not_le.2 ((memS P).1 h))
  let m : HeightOneSpectrum (𝓞 E) → ℕ := fun Q => (WithZero.log (Valued.v (y Q))).toNat
  let J : Ideal (𝓞 E) := ∏ Q ∈ S, Q.asIdeal ^ m Q
  have hJ : ¬ J ≤ P.asIdeal := by
    intro h
    obtain ⟨Q, hQ, hle⟩ := (Ideal.IsPrime.prod_le P.isPrime).1 h
    have h1 : Q.asIdeal ≤ P.asIdeal := by
      by_cases hm : m Q = 0
      · exfalso
        have h3 := (memS Q).1 hQ
        have hne : Valued.v (y Q) ≠ 0 := ne_of_gt (lt_trans zero_lt_one h3)
        rw [← WithZero.exp_log hne] at h3
        have h4 : (0 : ℤ) < WithZero.log (Valued.v (y Q)) := by
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h3
          exact h3
        have : m Q ≠ 0 := by
          show (WithZero.log (Valued.v (y Q))).toNat ≠ 0
          omega
        exact this hm
      · exact P.isPrime.le_of_pow_le hle
    have h2 : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h1)
    exact hPS (h2 ▸ hQ)
  obtain ⟨s, hsJ, hsP⟩ := SetLike.not_le_iff_exists.1 hJ
  refine ⟨s, hsP, fun Q => ?_⟩
  rw [map_mul, vAlg, HeightOneSpectrum.valuation_of_algebraMap]
  by_cases hQ : Q ∈ S
  · have hsQ : s ∈ Q.asIdeal ^ m Q :=
      (Finset.inf_le (f := fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal ^ m Q) hQ) (Ideal.prod_le_inf hsJ)
    have h1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem Q s (m Q)).2 hsQ
    have hne : Valued.v (y Q) ≠ 0 := ne_of_gt (lt_trans zero_lt_one ((memS Q).1 hQ))
    have h2 : Valued.v (y Q) ≤ WithZero.exp ((m Q : ℕ) : ℤ) := by
      rw [← WithZero.exp_log hne, WithZero.exp_le_exp]
      show WithZero.log (Valued.v (y Q)) ≤ ((WithZero.log (Valued.v (y Q))).toNat : ℤ)
      omega
    calc Q.intValuation s * Valued.v (y Q) ≤ WithZero.exp (-((m Q : ℕ) : ℤ)) * WithZero.exp ((m Q : ℕ) : ℤ) :=
          mul_le_mul' h1 h2
      _ = 1 := by rw [← WithZero.exp_add]; simp
  · have h1 : Valued.v (y Q) ≤ 1 := not_lt.1 fun h => hQ ((memS Q).2 h)
    exact mul_le_one' (HeightOneSpectrum.intValuation_le_one Q s) h1

theorem intAtA_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (x : AfE F E) :
    IntAtA (F := F) P x ↔ Valued.v (adAt F P x) ≤ 1 := by
  constructor
  · intro h
    exact GlobalTheory.TwU.IsAdIso.val_le (ι := afIso F E) ⟨afIso_tmul_one F E, mem_rInt_iff F E⟩ h
  · intro h
    obtain ⟨s, hs, hall⟩ := exists_clear P (afIso F E x) h
    refine ⟨s, hs, ?_⟩
    show _ ∈ RInt F E
    rw [mem_rInt_iff]
    intro Q
    have e : afIso F E (iA F E (algebraMap (𝓞 E) E s) * x) Q =
        algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) * afIso F E x Q := by
      rw [map_mul]
      have h2 : afIso F E (iA F E (algebraMap (𝓞 E) E s)) = algebraMap E _ (algebraMap (𝓞 E) E s) :=
        afIso_tmul_one F E _
      rw [h2]
      rfl
    rw [e]
    exact hall Q

theorem entry_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ))
    {n : ℕ} (N : ℕ) (z : GL (Fin n) (AfE F E)) (r s : Fin n) :
    IntAtA (F := F) P (iA F E (((qOf P : ℕ) : E) ^ N)⁻¹ * ((z : Matrix (Fin n) (Fin n) (AfE F E)) - 1) r s) ↔
      Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  rw [intAtA_iff, map_mul, adAt_inclE, Matrix.sub_apply, map_sub]
  have h1 : adAt F P ((1 : Matrix (Fin n) (Fin n) (AfE F E)) r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
    by_cases h : r = s
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
  rw [h1, map_mul, map_inv₀, map_pow, map_natCast, map_inv₀, map_pow, hq]
  have hE : (WithZero.exp (-1 : ℤ) ^ N)⁻¹ = WithZero.exp (N : ℤ) := by
    rw [← WithZero.exp_nsmul, ← WithZero.exp_neg]
    congr 1
    simp
  rw [hE]
  generalize Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) = x
  have hm : WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ) = 1 := by
    rw [← WithZero.exp_add]; simp
  constructor
  · intro h
    calc x = (WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ)) * x := by rw [hm, one_mul]
      _ = WithZero.exp (-(N : ℤ)) * (WithZero.exp (N : ℤ) * x) := mul_assoc _ _ _
      _ ≤ WithZero.exp (-(N : ℤ)) * 1 := mul_le_mul' le_rfl h
      _ = WithZero.exp (-(N : ℤ)) := mul_one _
  · intro h
    calc WithZero.exp (N : ℤ) * x ≤ WithZero.exp (N : ℤ) * WithZero.exp (-(N : ℤ)) := mul_le_mul' le_rfl h
      _ = 1 := by rw [mul_comm, hm]

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (n N : ℕ) (P : SBof I a) (z : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 ∧ Valued.v ((qOf P.1 : ℕ) : P.1.adicCompletion B.fields.E) = WithZero.exp (-1 : ℤ) ∧ (GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z ↔ ∀ r s, Valued.v (adAt B.host.F P.1 (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.1.adicCompletion B.fields.E)) r s) ≤ WithZero.exp (-(N : ℤ))) := by
  intro B X I hI l Z a n N P z
  have hseam : GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := by
    ext x
    exact GlobalTheory.TwU.mem_seamP (sm I l Z) P.1 x
  have hdeg := degOne_of_ok hI a P
  have hq := v_qOf P.1 hdeg.1 hdeg.2
  refine ⟨hseam, hq, ?_⟩
  rw [hseam]
  have i1 : NumberField ↥(I.rec7 l Z).host.F := inferInstance
  have i2 : NumberField (I.rec7 l Z).host.E := inferInstance
  exact forall_congr' fun r => forall_congr' fun s => @entry_iff (↥(I.rec7 l Z).host.F) (I.rec7 l Z).host.E _ i1 _ i2 _ P.1 hq n N z r s
end GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

theorem vT_notOver_SBof : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a) (v : HeightOneSpectrum (𝓞 B.host.F)), Formalism.L2.Col.IsOver v P.1 → ∀ (u : B.Word), ∀ P' ∈ (B.primes X).vT u, ¬ Formalism.L2.Col.IsOver v P' := by
  intro B X I hI a P v hP u P' hP' hv'
  have hok := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hT : ((B.primes X).T u : 𝓞 B.fields.E) ∉ P.1.asIdeal :=
    GlobalTheory.MuOffMove.level_notMem_rowSG hok hI.sel_ok (hI.T_mem u) P.2
  have hpi : (B.primes X).piT u ∈ P'.asIdeal := Formalism.L2.Col.decoFin_mem_of_mem_divs hP'
  have hTP' : ((B.primes X).T u : 𝓞 B.fields.E) ∈ P'.asIdeal := by
    rw [← hok.piT_norm u]
    exact Ideal.mul_mem_right _ _ hpi
  rcases Formalism.L2.Col.rll_over_cases B.sp.cm hP hv' with h | h
  · subst h
    exact hT hTP'
  · subst h
    rw [Formalism.L2.Col.mem_conjP, map_natCast] at hTP'
    exact hT hTP'

end GlobalTheory.Mem.Col2.AdT
end
