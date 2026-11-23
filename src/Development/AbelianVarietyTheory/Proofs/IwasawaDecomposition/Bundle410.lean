module

public import Formalism.LocalRingCardinality.Bundle006
public import Formalism.LocalRingCardinality.DataDIVDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle395
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.LocalToGlobal.Columns.Bundle015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.Columns.QthExistsBound
public import Formalism.LocalToGlobal.Columns.Bundle034
public import Formalism.LocalToGlobal.Columns.Bundle036
import Formalism.LocalToGlobal.Columns.TwQLevU
public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteAndCardQuotientAdicCompletionInteg
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle039
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle075
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344
public import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.Columns.ChainTwOk
public import Formalism.LocalToGlobal.Columns.ChainTwZero
public import Formalism.LocalToGlobal.Columns.Bundle028
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IndexAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018

@[expose] public section

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelCommensurable

theorem exists_nsmul_map_mem {K V W : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (A : Submodule (𝓞 K) W) (hA : A.FG) (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤)
    (f : W →ₗ[K] V) : ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ A, n • f x ∈ L := by
  classical
  obtain ⟨s, rfl⟩ := hA
  have h : ∀ x : W, ∃ n : ℕ, n ≠ 0 ∧ n • f x ∈ L := fun x =>
    GlobalTheory.Mem.Full.exists_nsmul_mem_of_span L (f x) (by rw [hL]; trivial)
  choose c hc0 hc using h
  refine ⟨∏ x ∈ s, c x, Finset.prod_ne_zero_iff.2 fun x _ => hc0 x, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem c (Finset.mem_coe.1 hy)
    rw [hk, mul_comm, mul_smul]
    exact L.toAddSubmonoid.nsmul_mem (hc y) k
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _), smul_add]; exact L.add_mem hy hz
  | smul r y _ hy =>
    rw [← algebraMap_smul K r y, map_smul, smul_comm, algebraMap_smul]
    exact L.smul_mem r hy


open GlobalTheory.LevelIndexCompare GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks in
theorem commensurable : ∀ (D : D7) (u : D.what₂.Word), (∀ v, ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)) → (∀ v, ∀ φ ∈ (D.mem u).A.Mram, LT.Uop D u 0 v φ = 0 → φ = 0) → ∀ w : D.what₂.places.Pl, ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧ ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x) := by
  classical
  intro D u hst hinj w
  have hex : ∀ v, ∃ g, IsScaledU D u w v g := fun v => (exists_isScaledU_iff D u w v).2 (hst v)
  choose g hg using hex
  haveI : Module.Finite D.what₂.LL (LT.Vl D u 0) := Module.Finite.of_basis ((D.fm u).lat 0).b
  have hgi : ∀ v, IsUnit (g v) := by
    intro v
    rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hg v x
    rw [hx, Submodule.coe_zero, map_zero] at h1
    have h2 := (smul_eq_zero.1 h1.symm).resolve_left (zpow_ne_zero _ (T_ne_zero D u))
    have h3 := hinj v _ x.2 h2
    exact Subtype.ext ((D.fm u).emb_inj 0 (h3.trans (map_zero _).symm))
  set G : Module.End D.what₂.LL (D.fm u).ramSub := ((LT.VVT D u w).toList.map g).prod ^ D.R.m with hG
  have hGu : IsUnit G := by
    refine IsUnit.pow _ (List.prod_isUnit fun a ha => ?_)
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 ha
    exact hgi v
  obtain ⟨H, hH⟩ := hGu.exists_right_inv
  have hmem : ∀ x, D.nuIn u x ∈ (D.fm u).ramSub := fun x => D.nuIn_range u ▸ ⟨x, rfl⟩
  let e : (D.div.Nu u).V →ₗ[D.what₂.LL] (D.fm u).ramSub := LinearMap.codRestrict _ (D.nuIn u) hmem
  obtain ⟨n₁, hn₁, h₁⟩ := exists_nsmul_map_mem (DV.MramL D u) (D.MramL_fg u) ((D.fm u).lat 0).L
    ((D.fm u).lat_good 0).2.2 ((D.fm u).ramSub.subtype ∘ₗ H ∘ₗ e)
  obtain ⟨n₂, hn₂, h₂⟩ := exists_nsmul_map_mem (DV.MramL D u) (D.MramL_fg u) ((D.fm u).lat 0).L
    ((D.fm u).lat_good 0).2.2 ((D.fm u).ramSub.subtype ∘ₗ G ∘ₗ e)
  refine ⟨n₁ * n₂, mul_ne_zero hn₁ hn₂, fun x hx => ?_, fun x hx => ?_⟩
  · rw [mem_Nlam_iff D u w g (fun v _ => hg v)]
    have hL : (((n₁ * n₂) • H (e x) : (D.fm u).ramSub) : LT.Vl D u 0) ∈ ((D.fm u).lat 0).L := by
      rw [mul_comm, mul_smul, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower]
      exact ((D.fm u).lat 0).L.toAddSubmonoid.nsmul_mem (h₁ x hx) n₂
    refine ⟨⟨_, ⟨Submodule.subset_span hL, ((n₁ * n₂) • H (e x)).2⟩⟩, ?_⟩
    show _ = ((G ((n₁ * n₂) • H (e x)) : (D.fm u).ramSub) : LT.Vl D u 0)
    rw [map_nsmul G, ← Module.End.mul_apply, hH, map_nsmul]
    rfl
  · rw [mem_Nlam_iff D u w g (fun v _ => hg v)] at hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨s, hs, hsy⟩ := D.inLoc_of_mem_locW w _ _ y.2.1
    obtain ⟨z, hz⟩ : (y : LT.Vl D u 0) ∈ LinearMap.range (D.nuIn u) := by
      rw [D.nuIn_range u]; exact y.2.2
    have hsm : ∀ t, D.nuIn u (s • t) = s • D.nuIn u t := fun t =>
      map_smul ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL)) s t
    have hzM : s • z ∈ DV.MramL D u := by
      show D.nuIn u (s • z) ∈ ((D.fm u).lat 0).L
      rw [hsm, hz]; exact hsy
    have h3 := h₂ _ hzM
    have hez : e z = incl D u w y := Subtype.ext hz
    have h4 : ((D.fm u).ramSub.subtype ∘ₗ G ∘ₗ e) (s • z) = s • D.nuIn u x := by
      rw [← algebraMap_smul D.what₂.LL s z, map_smul, algebraMap_smul, hy]
      show s • ((G (e z) : (D.fm u).ramSub) : LT.Vl D u 0) = _
      rw [hez]
    rw [h4] at h3
    refine ⟨s, hs, ?_⟩
    show D.nuIn u (s • (n₁ * n₂) • x) ∈ ((D.fm u).lat 0).L
    rw [hsm, map_nsmul, smul_comm, mul_smul]
    exact ((D.fm u).lat 0).L.toAddSubmonoid.nsmul_mem h3 n₁

end GlobalTheory.LevelCommensurable
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx


open Classical in

theorem thetaOpen_levQ : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}, L.Ok Ch sel mu cst G m2 → (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (j : ℕ) (b : L.β j), ThetaOpen (L.levQ j b) := by
  intro X Pr R Ch sel S mu cst L G m2 hL hQg j b P
  have hc : cst.Ok := hL.cst_ok
  let P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
  let h : AutY X R j := L.h j b P'
  have hPg := hQg P.1 P.2
  have hq := ciQ_mem P.1
  have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    intro h0
    exact P.1.ne_bot ((Ideal.absNorm_eq_zero_iff).1 h0)
  obtain ⟨a, ha⟩ := qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)
  obtain ⟨b', hb⟩ := qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h⁻¹ : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)
  obtain ⟨e, he⟩ := qth_exists_e P.1 hq0
  refine ⟨a + b' + e + 1, by omega, fun g hg => ?_⟩
  let r : AutY X R j := twZrExt (c := cOf R j) g.1
  have hr := qth_ext_close (c := cOf R j) P.1 g.1 _ hg
  have hrinv : r⁻¹ = twZrExt (c := cOf R j) (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 := LinearEquiv.ext fun v => rfl
  have hinv {E : Type} [Field E] [NumberField E] [StarRing E]
      (P : HeightOneSpectrum (𝓞 E)) {n N : ℕ} (g : ↥(GLint E n P))
      (hg : lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n)) :
      lqPrinc P N ((g⁻¹ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) := by
    unfold lqPrinc at hg ⊢
    intro i j
    set A := LinearMap.toMatrix' ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hA
    set B := LinearMap.toMatrix'
      ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hB
    have hBA : B * A = 1 := by
      rw [hA, hB, ← LinearMap.toMatrix'_comp]
      have hc : ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n).comp
          ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) = LinearMap.id := by
        refine LinearMap.ext fun x => ?_
        have hx : ((((g⁻¹ * g : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n)) x = x := by
          rw [inv_mul_cancel]
          rfl
        exact hx
      rw [hc, LinearMap.toMatrix'_id]
    have hBle : ∀ a k, P.valuation E (B a k) ≤ 1 := by
      intro a k
      rw [hB, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
      have hs : (Pi.single k (1 : E) : Sp E n) ∈ stdAt E n P := by
        show _ ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n)
        rw [mem_localization_standardLattice]
        intro t
        rw [qth_intAt_iff]
        by_cases h : t = k
        · subst h
          simp
        · simp [Pi.single_apply, h]
      have hmem : ((g⁻¹ : GLint E n P) : Sp E n ≃ₗ[E] Sp E n) ∈ stabL E n (stdAt E n P) :=
        (g⁻¹ : GLint E n P).2
      have h2 := (hmem _).2 hs
      have h3 := (mem_localization_standardLattice P _).1 h2 a
      rw [qth_intAt_iff] at h3
      exact h3
    have hBm : B - 1 = -(B * (A - 1)) := by
      rw [Matrix.mul_sub, hBA, Matrix.mul_one, neg_sub]
    rw [hBm, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
    refine Valuation.map_sum_le _ (fun k _ => ?_)
    rw [map_mul]
    calc _ ≤ 1 * P.valuation E ((A - 1) k j) := mul_le_mul' (hBle i k) le_rfl
      _ ≤ _ := by rw [one_mul]; exact hg k j
  
  have hr' := qth_ext_close (c := cOf R j) P.1 (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 _ (hinv P.1 g hg)
  have hy : QClose P.1 (qOf P.1) (h⁻¹ * r * h) := qth_conj_close P.1 (qOf P.1) h r a b' _ e ha hb hr he (by omega)
  have hy' : QClose P.1 (qOf P.1) (h⁻¹ * r * h)⁻¹ := by
    have e3 : (h⁻¹ * r * h)⁻¹ = h⁻¹ * r⁻¹ * h := by simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [e3, hrinv]
    exact qth_conj_close P.1 (qOf P.1) h _ a b' _ e ha hb hr' he (by omega)
  have hJ : h⁻¹ * r * h ∈ Jat (Pr := Pr) (R := R) cst.sharp j P.1 := by
    rw [twJat_Q cst.sharp j hPg]
    exact qth_mem_JQ P.1 (qOf P.1) hq0 (R.k + j) _ hy hy'
  have hC : r ∈ Loc.Cbe (Jat (Pr := Pr) (R := R) cst.sharp j P.1) h := by
    refine ⟨zeroExtension_mem_R1 g.1, ?_⟩
    show (MulAut.conj h⁻¹) r ∈ Jat (Pr := Pr) (R := R) cst.sharp j P.1
    simpa [MulAut.conj_apply] using hJ
  have hmem : g.1 ∈ prCat (Pr := Pr) cst.sharp j P.1 h := ⟨r, hC, twZrExt_inX g.1⟩
  have hH : g ∈ (L.levQ j b P).H := by
    rw [hL.grpQ j b P]
    exact Subgroup.mem_subgroupOf.2 hmem
  refine ⟨hH, ?_⟩
  apply Units.ext
  rw [hL.chrQ j b P ⟨g, hH⟩ r hC (fun x => twZrExt_inX g.1 x)]
  have hstd : r ∈ stabL X.E (R.N j + cOf R j) (stdAt X.E (R.N j + cOf R j) P.1) :=
    twZrExt_stab P.1 _ (fun v => ciMem_stdAt P.1 v) g.2
  have hint : IntAt P.1 (Loc.n1Arg r) := by
    unfold Loc.n1Arg
    refine ciIntAt_sum _ _ fun i _ => ?_
    have hv : r (Loc.eN X.E (R.N j + cOf R j) (R.N j + i + 1)) ∈ stdAt X.E (R.N j + cOf R j) P.1 :=
      (hstd _).2 (twZr_eN_mem P.1 _ _)
    rw [ciMem_stdAt] at hv
    unfold Loc.atN
    split_ifs
    · exact hv _
    · exact ciIntAt_zero
  unfold chiInv
  rw [hc.psi_int P' _ hint, inv_one, one_mul]
  unfold lamRow
  rw [if_neg hPg]
  have hlam {P : HeightOneSpectrum (𝓞 X.E)} (hq : ((qOf P : ℕ) : 𝓞 X.E) ∈ P.asIdeal) (hq0 : ((qOf P : ℕ) : X.E) ≠ 0) {j : ℕ}
      (ξ : (𝓞 X.E ⧸ P.asIdeal)ˣ →* X.Kˣ) (y : AutY X R j) (hy : QClose P (qOf P) y) :
      LocE.lamQB ξ (R.k + j) (R.N j) (y : Sp X.E (R.N j + cOf R j) →ₗ[X.E] Sp X.E (R.N j + cOf R j)) = 1 := by
    classical
    unfold LocE.lamQB
    set D : Matrix (Fin (R.N j - (R.k + j))) (Fin (R.N j - (R.k + j))) X.E := Matrix.of fun s t : Fin (R.N j - (R.k + j)) =>
      Loc.atN ((y : Sp X.E (R.N j + cOf R j) →ₗ[X.E] Sp X.E (R.N j + cOf R j)) (Loc.eN X.E (R.N j + cOf R j) (R.k + j + t.1))) (R.k + j + s.1) with hD
    have hent : ∀ s t : Fin (R.N j - (R.k + j)), IntAt P (D s t) ∧ redP P (D s t) = (1 : Matrix _ _ (𝓞 X.E ⧸ P.asIdeal)) s t := by
      intro s t
      have hs : R.k + j + s.1 < R.N j + cOf R j := by have := s.2; omega
      have ht : R.k + j + t.1 < R.N j + cOf R j := by have := t.2; omega
      have e1 : Loc.eN X.E (R.N j + cOf R j) (R.k + j + t.1) = Pi.single ⟨R.k + j + t.1, ht⟩ 1 := by
        funext l
        unfold Loc.eN
        rw [Pi.single_apply]
        congr 1
        apply propext
        constructor
        · intro h; exact Fin.ext h
        · intro h; rw [h]
      have e2 : D s t = ((toGLm X.E (R.N j + cOf R j) y : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E) ⟨R.k + j + s.1, hs⟩ ⟨R.k + j + t.1, ht⟩ := by
        rw [qsp_toGLm_apply, hD, Matrix.of_apply, e1]
        unfold Loc.atN
        rw [dite_eq_left hs]
        rfl
      obtain ⟨h1, h2⟩ := qth_red_entry P (qOf P) hq0 hq hy ⟨R.k + j + s.1, hs⟩ ⟨R.k + j + t.1, ht⟩
      rw [e2]
      refine ⟨h1, ?_⟩
      rw [h2, Matrix.one_apply, Matrix.one_apply]
      by_cases hst : s = t
      · rw [if_pos (Fin.ext (by simp [hst])), if_pos hst, redP_one]
      · rw [if_neg (fun h => hst (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))), if_neg hst, redP_zero]
    have hdet : redP P D.det = 1 := by
      rw [redP_det D fun s t => (hent s t).1]
      have : D.map (redP P) = 1 := Matrix.ext fun s t => (hent s t).2
      rw [this, Matrix.det_one]
    unfold LocE.unitV
    have hu : IsUnit (redP P D.det) := by rw [hdet]; exact isUnit_one
    rw [dite_eq_left hu]
    have : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hdet]; rfl)
    rw [this, map_one, Units.val_one, inv_one]
  exact hlam hq hq0 _ _ hy

end GlobalTheory.Mem.Col2.ChEx
end
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.ParGroup

variable {F : Type} [Field F] (O : Subring F) (ϖ : F)

def InW (x : F) : Prop := ∃ o ∈ O, x = ϖ * o

theorem inW_sum {ι : Type} (s : Finset ι) (f : ι → F) (h : ∀ i ∈ s, InW O ϖ (f i)) :
    InW O ϖ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, O.zero_mem, by simp⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨o₁, ho₁, e₁⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨o₂, ho₂, e₂⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact ⟨o₁ + o₂, O.add_mem ho₁ ho₂, by rw [e₁, e₂, mul_add]⟩

theorem inW_mul_right {x a : F} (hx : InW O ϖ x) (ha : a ∈ O) : InW O ϖ (x * a) := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨o * a, O.mul_mem ho ha, by ring⟩

theorem inW_mul_left {x a : F} (ha : a ∈ O) (hx : InW O ϖ x) : InW O ϖ (a * x) := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨a * o, O.mul_mem ha ho, by ring⟩

theorem mul_mem_parJ {r c : ℕ} {k k' : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c)
    (hk' : k' ∈ parJ O ϖ r c) : k * k' ∈ parJ O ϖ r c := by
  obtain ⟨hkG, hkW⟩ := hk
  obtain ⟨hkG', hkW'⟩ := hk'
  refine ⟨(GLint O (r + c)).mul_mem hkG hkG', ?_⟩
  have hI : IsInt O (k : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG.1
  have hI' : IsInt O (k' : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG'.1
  intro i j
  show InW O ϖ _
  simp only [bDA, Matrix.submatrix_apply, Units.val_mul, Matrix.mul_apply]
  apply inW_sum
  intro l _
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · exact inW_mul_right O ϖ (hkW i l) (hI' _ _)
  · exact inW_mul_left O ϖ (hI _ _) (hkW' l j)
private theorem lower_block_eq_zero_of_mul_eq_one {R : Type} [CommRing R] {r c : ℕ}
    (K N : Matrix (Fin (r + c)) (Fin (r + c)) R) (hKN : K * N = 1)
    (hK : ∀ i j, K (Fin.natAdd r i) (Fin.castAdd c j) = 0) (i : Fin c) (j : Fin r) :
    N (Fin.natAdd r i) (Fin.castAdd c j) = 0 := by
  let D : Matrix (Fin c) (Fin c) R := K.submatrix (Fin.natAdd r) (Fin.natAdd r)
  let T : Matrix (Fin c) (Fin c) R := N.submatrix (Fin.natAdd r) (Fin.natAdd r)
  let S : Matrix (Fin c) (Fin r) R := N.submatrix (Fin.natAdd r) (Fin.castAdd c)
  have key : ∀ a b, (K * N) (Fin.natAdd r a) b =
      ∑ l : Fin c, K (Fin.natAdd r a) (Fin.natAdd r l) * N (Fin.natAdd r l) b := by
    intro a b
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    simp [hK]
  have hDT : D * T = 1 := by
    ext a b
    have h := key a (Fin.natAdd r b)
    rw [hKN] at h
    simp only [D, T, Matrix.mul_apply, Matrix.submatrix_apply]
    rw [← h]
    by_cases hab : a = b
    · subst hab
      simp
    · have hne : Fin.natAdd r a ≠ Fin.natAdd r b := by
        intro e
        apply hab
        ext
        have := congrArg Fin.val e
        simp at this
        omega
      rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hab]
  have hDS : D * S = 0 := by
    ext a b
    have h := key a (Fin.castAdd c b)
    rw [hKN] at h
    have hne : Fin.natAdd r a ≠ Fin.castAdd c b := by
      intro e
      have := congrArg Fin.val e
      have hb := b.isLt
      simp at this
      omega
    rw [Matrix.one_apply_ne hne] at h
    simp only [D, S, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.zero_apply]
    exact h.symm
  have hTD : T * D = 1 := by
    first
    | exact mul_eq_one_comm.mp hDT
    | rw [← Matrix.inv_eq_right_inv hDT]
      exact Matrix.nonsing_inv_mul D (Matrix.isUnit_det_of_right_inverse hDT)
  have hS : S = 0 := by
    calc S = (T * D) * S := by rw [hTD, Matrix.one_mul]
      _ = T * (D * S) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hDS, Matrix.mul_zero]
  exact congrFun (congrFun hS i) j

theorem inv_mem_parJ {r c : ℕ} {k : GL (Fin (r + c)) F} (hϖ : ϖ ∈ O) (hk : k ∈ parJ O ϖ r c) :
    k⁻¹ ∈ parJ O ϖ r c := by
  obtain ⟨hkG, hkW⟩ := hk
  refine ⟨(GLint O (r + c)).inv_mem hkG, ?_⟩
  have hI : IsInt O (k : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG.1
  have hJ : IsInt O ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG.2
  let KO : Matrix (Fin (r + c)) (Fin (r + c)) O := fun a b => ⟨(k : Matrix (Fin (r + c)) (Fin (r + c)) F) a b, hI a b⟩
  let NO : Matrix (Fin (r + c)) (Fin (r + c)) O :=
    fun a b => ⟨((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) a b, hJ a b⟩
  have hKN : KO * NO = 1 := by
    apply Matrix.map_injective (f := O.subtype) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have e1 : KO.map O.subtype = (k : Matrix (Fin (r + c)) (Fin (r + c)) F) := by ext; rfl
    have e2 : NO.map O.subtype = ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) := by ext; rfl
    rw [e1, e2, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  let π := Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)})
  have hKNb : KO.map π * NO.map π = 1 := by
    rw [← Matrix.map_mul, hKN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hK0 : ∀ i j, KO.map π (Fin.natAdd r i) (Fin.castAdd c j) = 0 := by
    intro i j
    obtain ⟨o, ho, e⟩ := hkW i j
    rw [Matrix.map_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨⟨o, ho⟩, Subtype.ext ?_⟩
    simp only [bDA, Matrix.submatrix_apply] at e
    simp only [KO, Subring.coe_mul, e]
    ring
  intro i j
  have h0 := lower_block_eq_zero_of_mul_eq_one (KO.map π) (NO.map π) hKNb hK0 i j
  rw [Matrix.map_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
  obtain ⟨⟨o, ho⟩, e⟩ := h0
  refine ⟨o, ho, ?_⟩
  have e' := congrArg Subtype.val e
  simp only [NO, Subring.coe_mul] at e'
  simp only [bDA, Matrix.submatrix_apply]
  rw [← e']
  ring

theorem parJ_mul_inv : ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F), ϖ ∈ O → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) F),
    k ∈ parJ O ϖ r c → k' ∈ parJ O ϖ r c → k * k' ∈ parJ O ϖ r c ∧ k⁻¹ ∈ parJ O ϖ r c := by
  intro F _ O ϖ hϖ r c k k' hk hk'
  exact ⟨mul_mem_parJ O ϖ hk hk', inv_mem_parJ O ϖ hϖ hk⟩

end GlobalTheory.ParGroup
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.ResidueCardUnif

theorem card_kF_piP : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (h : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ∈ OP P), Nat.card (kF (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) h) = qP P := by
  intro L _ _ P h
  have ha : Valued.v ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    unif_spec P
  have h1 : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ∈ P.adicCompletionIntegers L := h
  have e : IsLocalRing.maximalIdeal (P.adicCompletionIntegers L) = Ideal.span {⟨_, h1⟩} := by
    ext y
    rw [GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers P
      (by rw [ha]; exact WithZero.exp_ne_zero)]
    rw [ha, ← GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp]
    exact Valuation.mem_maximalIdeal_iff _ _
  have c := GlobalTheory.GaugeProdFormula.card_residue L P
  rw [IsLocalRing.ResidueField, e] at c
  exact c

end GlobalTheory.ResidueCardUnif
end
