module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle148
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle319
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle212
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle188
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle131
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle323
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle133
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle103
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle081
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle140
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle147
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle060
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle028
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle080
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle091
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle092
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.CuspFrameOneType

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨(Formalism.UG.stabGL I.Lf).one_mem, fun y _ => ⟨0, I.Lf.zero_mem, ?_⟩⟩
  have : I.fmat 1 = 1 := rfl
  simp [this]

theorem re_fixed (B : RowsAut) : ∀ k ∈ B.I.Kg B.g, (B.R (1, k)).comp B.Re = B.Re := by
  intro k hk
  obtain ⟨hT2, -, hsc, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨R1, Rm, Rn, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨-, -, -, -, -, hinv, -⟩ := B.e_adm
  obtain ⟨-, hT⟩ := B.Re_spec
  have p1 : (fun g : B.I.Gf => B.R (1, g)) 1 = 1 := R1
  have pm : ∀ a b : B.I.Gf, B.R (1, a * b) = B.R (1, a) * B.R (1, b) := by
    intro a b; rw [← Rm]; simp
  have pn : ∀ (g : B.I.Gf) v, ‖B.R (1, g) v‖ = ‖v‖ := fun g v => Rn _ v
  exact GlobalTheory.IdemProj.op_fixed B.μf (fun g => B.R (1, g)) p1 pm pn B.e B.Re hT k
    (fun x => by simpa using hinv x k hk 1 (one_mem_Kg B.I B.g))

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hl : LocDec B h) (hb : HBig B 40 h) : Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hm, hi⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have h0 := hi 0 le_rfl (fun v => by
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with hq | hq
    · exact Or.inl hq
    · right
      have hle : rkR (B.I.ε v) ≤ B.I.n := by
        unfold rkR
        refine (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
      have h1 : (0 : ℝ) < rkR (B.I.ε v) := by exact_mod_cast hq
      have h2 : ((rkR (B.I.ε v) : ℕ) : ℝ) ≤ B.I.n := by exact_mod_cast hle
      have h3 := Real.sqrt_pos.2 h1
      have h4 := hb v
      have h5 : (0 : ℝ) < B.I.n := h1.trans_le h2
      have h6 : (B.I.n : ℝ) * rkR (B.I.ε v) ≤ (B.I.n : ℝ) ^ 2 := by nlinarith
      have h7 : 0 < (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h6 h3.le])
  simp only [zero_mul, Real.exp_zero, mul_one] at h0
  exact h0.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hm)

theorem cuspidal_frame : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∃ Rφ : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund, B.I.IsRConv B.μf B.fund B.R (phe B d) Rφ ∧ ∃ T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames.IsCuspidalFrame B Rφ T := by
  intro B d h hd hS _ hgap hl hb hfin
  obtain ⟨-, hcomm, ⟨Rφ, hR⟩, hP⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd (integrable_ph B d h hd hl hb)
  obtain ⟨hproj, hfix, hex, -, -⟩ := hP Rφ hR
  obtain ⟨hU, hirr, -, hw, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  have hle : B.I.eHom B.σs B.μf B.fund B.R B.Re ≤ B.I.HomS B.σs B.μf B.fund B.R := by
    rintro _ ⟨A, hA, rfl⟩ g
    show (B.Re.comp A).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  obtain ⟨T, hT, hn, ho, hsp⟩ := GlobalTheory.IntertwinerFrame.exists_orthonormal_frame B d hd hfin hle
  obtain ⟨S, hSm, hScl, hSst, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  refine ⟨Rφ, hR, T, hT, fun i => hle (hT i), hn, ho, hsp, fun i u => ?_, fun i u k hk => ?_, ?_, ?_⟩
  · have hw' : T i (B.tens B.w) ∈ S := by
      rw [hSm, ← hfix _ (hT i)]
      exact (GlobalTheory.T.convolution_range_cuspidal_of_lowestKType B d h hd hS hgap hl hb hfin Rφ hR _).2
    have hcl : IsClosed ((S.comap (T i : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) : Submodule ℂ B.Hs) : Set B.Hs) :=
      hScl.preimage (T i).continuous
    rcases hirr _ hcl (fun g v hv => by
      have e := congrArg (fun A : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => A v) (hle (hT i) g)
      simp only [ContinuousLinearMap.comp_apply] at e
      show T i (B.σs g v) ∈ S
      rw [e]
      exact hSst _ _ hv) with h0 | h0
    · have : B.tens B.w ∈ S.comap (T i : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) := hw'
      rw [h0, Submodule.mem_bot] at this
      rw [this] at hw
      simp at hw
    · have : u ∈ S.comap (T i : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) := by rw [h0]; trivial
      exact (hSm _).1 this
  · obtain ⟨A, -, hA⟩ := hT i
    rw [← hA]
    exact congrArg (fun C : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => C (A u)) (re_fixed B k hk)
  · exact ⟨fun i => by rw [hn, hw], fun i j hij => ho i j hij _ _⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨_, hfix _ (hT i)⟩
    · rintro _ ⟨z, rfl⟩
      have hz : Rφ (Rφ z) = Rφ z :=
        congrArg (fun C : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => C z) hproj.1
      obtain ⟨A, ⟨hA, hAw⟩, -⟩ := hex _ hz
      rw [← hsp] at hA
      have := Submodule.mem_map_of_mem
        (f := (ContinuousLinearMap.apply ℂ (B.I.L2 B.μf B.fund) (B.tens B.w)).toLinearMap) hA
      rw [Submodule.map_span, ← Set.range_comp] at this
      show Rφ z ∈ _
      rw [← hAw]
      exact this

end GlobalTheory.Dec.CuspFrameOneType
end
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CovDomGrp

variable {D : D7} (X : HidaSetting D)

theorem crdH_injective : Function.Injective (crdH X) := by
  intro y y' h
  rw [← vecOf_crdH X y, h, vecOf_crdH]

theorem mul_eOf_Pc_apply (u : D.what₂.Word)
    (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E)
    (i : Fin (2 * D.R.rS + D.R.k + 1)) (a : Fin D.R.rS) :
    (γ * GlobalTheory.SgAlg.eOf (Pc X u)) i a = (γ *ᵥ crdH X (X.eX a)) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, GlobalTheory.SgAlg.eOf, Pc]

theorem eOf_Pc_mul_apply (u : D.what₂.Word) (ν : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (i : Fin (2 * D.R.rS + D.R.k + 1)) (a : Fin D.R.rS) :
    (GlobalTheory.SgAlg.eOf (Pc X u) * ν) i a = crdH X (∑ b, ν b a • X.eX b) i := by

  rw [← coordEquiv_symm_apply, map_sum]
  simp [Matrix.mul_apply, GlobalTheory.SgAlg.eOf, Pc, coordEquiv_symm_apply, Finset.sum_apply, mul_comm]

theorem xflag_Fu (u : D.what₂.Word) (j : ℕ) :
    Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) j = Submodule.span D.host.E (X.eX '' {i | i.1 < j}) := by
  show (X.Fu u).Xa j = _
  unfold FlagG.Xa
  rw [X.Fu_e]

theorem flag_iff {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E) :
    (∀ y, crdH X (n y) = γ *ᵥ crdH X y) →
    ((∃ ν, GlobalTheory.SgAlg.IsUp ν ∧ γ * GlobalTheory.SgAlg.eOf (Pc X u) = GlobalTheory.SgAlg.eOf (Pc X u) * ν) ↔
      ∀ j, ∀ x ∈ Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) (j + 1), n x - x ∈ Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) j) := by
  intro hγ
  have hcol : ∀ ν : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E,
      γ * GlobalTheory.SgAlg.eOf (Pc X u) = GlobalTheory.SgAlg.eOf (Pc X u) * ν ↔ ∀ a, n (X.eX a) = ∑ b, ν b a • X.eX b := by
    intro ν
    constructor
    · intro h a
      apply crdH_injective X
      funext i
      rw [← eOf_Pc_mul_apply, ← h, mul_eOf_Pc_apply, hγ]
    · intro h
      ext i a
      rw [mul_eOf_Pc_apply, eOf_Pc_mul_apply, ← h, hγ]
  simp only [xflag_Fu]
  constructor
  · rintro ⟨ν, hν, h⟩
    have h1 := (hcol ν).1 h
    have hstep : ∀ a : Fin D.R.rS,
        n (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < a.1}) := by
      intro a
      rw [h1 a]
      have hs : ∑ b, ν b a • X.eX b - X.eX a = ∑ b, (ν b a - if b = a then 1 else 0) • X.eX b := by
        simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
      rw [hs]
      refine Submodule.sum_mem _ fun b _ => ?_
      rcases lt_trichotomy b a with hb | rfl | hb
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
      · simp [(hν b b).2 rfl]
      · simp [(hν b a).1 hb, hb.ne']
    intro j x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      have hij : i.1 ≤ j := Nat.lt_succ_iff.mp hi
      have hsub : {k : Fin D.R.rS | k.1 < i.1} ⊆ {k : Fin D.R.rS | k.1 < j} :=
        fun k (hk : k.1 < i.1) => (lt_of_lt_of_le hk hij : k.1 < j)
      exact Submodule.span_mono (Set.image_mono hsub) (hstep i)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      convert Submodule.add_mem _ hx hy using 1
      abel
    | smul c x _ hx =>
      rw [map_smul]
      convert Submodule.smul_mem _ c hx using 1
      rw [smul_sub]
  · intro h
    have ha : ∀ a : Fin D.R.rS, ∃ l ∈ Finsupp.supported D.host.E D.host.E {i : Fin D.R.rS | i.1 < a.1},
        Finsupp.linearCombination D.host.E X.eX l = n (X.eX a) - X.eX a := by
      intro a
      rw [← Finsupp.mem_span_image_iff_linearCombination]
      exact h a.1 (X.eX a) (Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩)
    choose l hl hl2 using ha
    refine ⟨fun b a => l a b + if b = a then 1 else 0, ?_, (hcol _).2 fun a => ?_⟩
    · intro i j
      constructor
      · intro hji
        have h0 : l j i = 0 := (Finsupp.mem_supported' _ _).1 (hl j) i (fun hh => absurd (hh : i.1 < j.1) (not_lt.2 (le_of_lt hji)))
        simp [h0, (ne_of_lt hji).symm]
      · rintro rfl
        have h0 : l i i = 0 := (Finsupp.mem_supported' _ _).1 (hl i) i (fun hh => lt_irrefl i.1 hh)
        simp [h0]
    · have hlc := hl2 a
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hlc
      simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hlc]
      abel

end GlobalTheory.CovDomGrp
end
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDomGrp

variable {D : D7} (X : HidaSetting D)

theorem eOf_Pc_apply (u : D.what₂.Word) (i : Fin (2 * D.R.rS + D.R.k + 1)) (a : Fin D.R.rS) :
    GlobalTheory.SgAlg.eOf (Pc X u) i a = crdH X (X.eX a) i := by
  simp [GlobalTheory.SgAlg.eOf, Pc]

theorem Xsp_Fu_eq_span (u : D.what₂.Word) :
    Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range X.eX) := by
  show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
  rw [X.Fu_e]

theorem vecOf_eOf_mulVec (u : D.what₂.Word) (c : Fin D.R.rS → D.host.E) :
    vecOf X (GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c) = ∑ a, c a • X.eX a := by
  have hcol : GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c = ∑ a, c a • crdH X (X.eX a) := by
    ext i
    simp [Matrix.mulVec, dotProduct, eOf_Pc_apply, Finset.sum_apply, mul_comm]

  rw [hcol, map_sum]
  simp only [map_smul, vecOf_crdH]

theorem cT_eOf_mulVec_apply (u : D.what₂.Word) (v : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) (a : Fin D.R.rS) :
    ((GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.SgAlg.eOf (Pc X u)) * Jc X) *ᵥ v) a
      = (VS D).hT (X.eX a) (vecOf X v) := by
  rw [← Matrix.mulVec_mulVec]
  conv_rhs => rw [← vecOf_crdH X (X.eX a), hT_vecOf]
  simp only [GlobalTheory.SgAlg.form, GlobalTheory.SgAlg.cT, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.map_apply, eOf_Pc_apply]

theorem mem_orth_span_iff (y : (VS D).V) :
    y ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Submodule.span D.host.E (Set.range X.eX)) ↔
      ∀ a, (VS D).hT (X.eX a) y = 0 := by
  simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h a
    exact h _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact h a
    | zero => simp
    | add x z _ _ hx hz => simp [hx, hz]
    | smul c x _ hx => simp [hx]

theorem orth_cond_iff_coord : ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ((∀ v, (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.SgAlg.eOf (Pc X u)) * Jc X) *ᵥ v = 0 → ∃ c, γ *ᵥ v - v = GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c) ↔ ∀ x ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u))), n x - x ∈ Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u))) := by
  intro D X u n γ hγ
  have inj : Function.Injective (vecOf X) := fun a b h => by
    simpa [crdH_vecOf] using congrArg (crdH X) h
  have hperp : ∀ v, (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.SgAlg.eOf (Pc X u)) * Jc X) *ᵥ v = 0 ↔
      ∀ a, (VS D).hT (X.eX a) (vecOf X v) = 0 := by
    intro v
    constructor
    · intro h a
      have h' := congrFun h a
      rwa [cT_eOf_mulVec_apply] at h'
    · intro h
      funext a
      rw [cT_eOf_mulVec_apply]
      exact h a
  have himg : ∀ v c, (γ *ᵥ v - v = GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c ↔
      n (vecOf X v) - vecOf X v = ∑ a, c a • X.eX a) := by
    intro v c
    rw [← vecOf_eOf_mulVec X u c, n_vecOf hγ, ← map_sub]
    exact inj.eq_iff.symm
  rw [Xsp_Fu_eq_span X u]
  constructor
  · intro H x hx
    rw [mem_orth_span_iff X x] at hx
    obtain ⟨c, hc⟩ := H (crdH X x) ((hperp _).2 (by simpa [vecOf_crdH] using hx))
    rw [himg, vecOf_crdH] at hc
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, hc.symm⟩
  · intro H v hv
    have hx : vecOf X v ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Submodule.span D.host.E (Set.range X.eX)) :=
      (mem_orth_span_iff X (vecOf X v)).2 ((hperp v).1 hv)
    have hm := H _ hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hm
    obtain ⟨c, hc⟩ := hm
    exact ⟨c, (himg v c).2 hc.symm⟩

end GlobalTheory.CovDomGrp
end
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDomGrp

theorem form_mulVec_mulVec {E : Type} [CommRing E] (σ : E →+* E) {m : ℕ} (J γ : Matrix (Fin m) (Fin m) E)
    (x y : Fin m → E) :
    GlobalTheory.SgAlg.form σ J (γ *ᵥ x) (γ *ᵥ y) = GlobalTheory.SgAlg.form σ (GlobalTheory.SgAlg.cT σ γ * J * γ) x y := by
  have h : (fun i => σ ((γ *ᵥ y) i)) = (fun i => σ (y i)) ᵥ* GlobalTheory.SgAlg.cT σ γ := by
    funext i
    simp [GlobalTheory.SgAlg.cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  simp only [GlobalTheory.SgAlg.form]
  rw [h, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem form_single_single {E : Type} [CommRing E] (σ : E →+* E) {m : ℕ} (M : Matrix (Fin m) (Fin m) E)
    (i j : Fin m) : GlobalTheory.SgAlg.form σ M (Pi.single j 1) (Pi.single i 1) = M i j := by
  simp [GlobalTheory.SgAlg.form, dotProduct, Pi.single_apply, Matrix.mulVec_single]

theorem isUn_iff_mem_isom {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E)
    (hγ : ∀ y, crdH X (n y) = γ *ᵥ crdH X y) :
    GlobalTheory.SgAlg.IsUn (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) γ ↔ n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
  constructor
  · intro hU
    change ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y
    intro x y
    rw [← vecOf_crdH X x, ← vecOf_crdH X y, n_vecOf hγ, n_vecOf hγ, hT_vecOf, hT_vecOf,
      form_mulVec_mulVec, hU]
  · intro hn
    have hn' : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hn
    ext i j
    rw [← form_single_single _ (GlobalTheory.SgAlg.cT _ γ * Jc X * γ) i j, ← form_mulVec_mulVec,
      ← hT_vecOf X, ← n_vecOf hγ, ← n_vecOf hγ, hn', hT_vecOf, form_single_single]

end GlobalTheory.CovDomGrp
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomProdPart

theorem product_moment_first : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (m : ℕ) (hm : m ≤ r + 1) ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (lb ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a : Fin m, lenA k r z (Matrix.of x) (Fin.castLE hm a) ^ 2) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ m) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS m hm ν hν hnz
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hNum := hS.1
  have hFam := hS.2.1
  have hSide := hS.2.2.1
  have hSF := hS.2.2.2
  have hk : 1 ≤ k := hNum.1
  have hν0 : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) hν
  obtain ⟨Q, hQ⟩ := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).1 hk
  have hQu : IsUnit Q := hQ.1.1
  have hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E, hE⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r _ _ (R ν') (hFam ν' h') Q hQu
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hE
  have hDS := hFam ν hν0
  obtain ⟨w, hw1, -, hwK, hwF⟩ := GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries hK k r _ _ (R ν) hDS Q (E ν) hQ (hE ν hν0).1
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hk hDS Q (E ν) hQ (hE ν hν0).1
  have hLev := GlobalTheory.lev_zero_of_kHighest _ _ _ (E ν) _ w hMod.1 hMod.2.1 hwK hwF
  have hw1' : ‖(w : (R ν).H)‖ = 1 := hw1
  have hwsm : (w : (R ν).H) ∈ (R ν).sm := w.2
  refine ⟨(w : (R ν).H), hwsm, hw1', ?_⟩
  obtain ⟨hG, -, hlen, hmeas⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide
  obtain ⟨hBeL, hdg, -⟩ := hSF ν hν0
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hSide.2.1
  obtain ⟨⟨hb1, hb2, -, -, -⟩, -⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  have hq2 : ∀ q ≤ (r + 1) ^ 2, 0 + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 := by
    intro q hq
    have : (r + 1) ^ 2 ≤ (2 * r + k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hb : (1 : ℝ) ≤ b := by linarith
  have hA : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) := by
    have : 0 ≤ bv := by linarith
    positivity
  have hmain := GlobalTheory.T.initial_lengths_product_moment_le (Formalism.QuantumDeterminants.Mt k r) νq r m hm (fun a x => lenA k r z (Matrix.of x) a)
    (fun x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)
    (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) (b ^ 2)
    hlen
    (fun a => hG.mono fun x hx => (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.1 a)
    (((hmeas (l ν) hBeL.1 w hwsm).norm.aemeasurable.pow_const 2).const_mul _)
    (fun x => mul_nonneg hdg.le (by positivity))
    (by
      have := ((GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν0).2 hnz).2 w hwsm
      simpa only [one_mul, hw1', one_pow, ENNReal.ofReal_one] using this)
    hA (one_le_pow₀ hb)
    (fun q hq => by
      have := GlobalTheory.T.family_setup_cayley_recursion hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE q ν
        (by omega) 0 (hq2 q hq) w hLev
      simpa only [hw1, one_pow, mul_one] using this)
    (fun a q hq => by
      have := GlobalTheory.T.family_setup_cayley_bound hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν0
        0 q (hq2 q hq) a w hLev
      simpa only [hw1, one_pow, mul_one] using this)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  exact pow_le_pow_left₀ (mul_nonneg hA (by positivity))
    (GlobalTheory.T.numericalFamily_productBound_constant_le k r lam u b bv ga h q0 _ hNum hT) _

end GlobalTheory.MomProdPart
end
