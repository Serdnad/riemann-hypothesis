module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle054
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle080
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle081
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem gcl_slice_iter {r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : (Fin r → ℂ) × ℂ → V) (s : Set ((Fin r → ℂ) × ℂ)) (hs : IsOpen s)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F s) (q : (Fin r → ℂ) × ℂ) (hq : q ∈ s) (j : ℕ) :
    iteratedFDeriv ℝ j (fun ζ => F (q.1, ζ)) q.2 =
      (iteratedFDeriv ℝ j F q).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ (Fin r → ℂ) ℂ) := by
  let a : (Fin r → ℂ) × ℂ := (q.1, 0)
  let L : ℂ →L[ℝ] (Fin r → ℂ) × ℂ := ContinuousLinearMap.inr ℝ (Fin r → ℂ) ℂ
  let G : (Fin r → ℂ) × ℂ → V := fun p => F (a + p)
  let s' : Set ((Fin r → ℂ) × ℂ) := (fun p => a + p) ⁻¹' s
  have hs' : IsOpen s' := hs.preimage (continuous_const.add continuous_id)
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G s' :=
    hF.comp ((contDiff_const.add contDiff_id).contDiffOn) (fun p hp => hp)
  have hslice : (fun ζ : ℂ => F (q.1, ζ)) = G ∘ L := by
    funext ζ
    simp [G, a, L]
  have hq' : L q.2 ∈ s' := by
    show a + L q.2 ∈ s
    simpa [a, L] using hq
  have hpre : IsOpen (L ⁻¹' s') := hs'.preimage L.continuous
  have hmem : q.2 ∈ L ⁻¹' s' := hq'
  rw [hslice, ← iteratedFDerivWithin_of_isOpen j hpre hmem,
    L.iteratedFDerivWithin_comp_right hG hs'.uniqueDiffOn hpre.uniqueDiffOn hq'
      (by exact_mod_cast (le_top : ((j : ℕ∞)) ≤ ⊤)),
    iteratedFDerivWithin_of_isOpen j hs' hq']
  have hGq : iteratedFDeriv ℝ j G (L q.2) = iteratedFDeriv ℝ j F q := by
    show iteratedFDeriv ℝ j (fun p => F (a + p)) (L q.2) = _
    rw [iteratedFDeriv_comp_add_left']
    show iteratedFDeriv ℝ j F (a + L q.2) = _
    congr 1
    ext <;> simp [a, L]
  rw [hGq]

theorem gcl_isRadDiff {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hRB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π')
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (hT : RadDZ P Bs T) :
    NF.IsRadDiff P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' T := by
  obtain ⟨n, A, hA, hT'⟩ := hT
  have hmem : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp))) (NF.QR P.k P.r Bs.z Bs.z') :=
    fun Φ => (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB Φ Φ.2).1
  have hopen : IsOpen (NF.QR P.k P.r Bs.z Bs.z') := by
    have h1 : IsOpen (Formalism.QuantumDeterminants.OmX P.r) := by
      have h2 : Formalism.QuantumDeterminants.OmX P.r = ⋂ l, {x : Fin P.r → ℂ | x l ≠ 0} := by
        ext x
        simp [Formalism.QuantumDeterminants.OmX]
      rw [h2]
      exact isOpen_iInter_of_finite (fun l => isOpen_ne_fun (continuous_apply l) continuous_const)
    exact (h1.preimage continuous_fst).inter
      (isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd))
  refine ⟨n, fun j q => (A j q.2).comp (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin j => ContinuousLinearMap.inr ℝ (Fin P.r → ℂ) ℂ)), ?_, ?_⟩
  · intro j
    have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (Fin P.r → ℂ) × ℂ => A j q.2)
        (NF.QR P.k P.r Bs.z Bs.z') :=
      (hA j).comp contDiff_snd.contDiffOn (fun q hq => hq.2)
    exact hA'.clm_comp contDiffOn_const
  · intro Φ q hq
    rw [hT' Φ q hq]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [gcl_slice_iter _ _ hopen (hmem Φ) q hq j]
    simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.compContinuousLinearMapL_apply]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

namespace Formalism.FourierDecayAlt.P.GermRealisation

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

def ptX (s : ℕ) (h : C.LPt) (x : ℂ) : C.LPt := h ++ [(s - 1, x⁻¹)]

def utOf {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (s : ℕ) (V : C.LPt → ℂ → H) (h : C.LPt)
    (x D : ℂ) : H :=
  ((‖x‖ ^ (s - 1) : ℝ) : ℂ) • V (ptX s h x) (x ^ (s - 1) * D)

theorem cvec_utOf {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (s : ℕ) (V : C.LPt → ℂ → H)
    (h : C.LPt) (x : ℂ) (hx : x ≠ 0) : cvec s (utOf s V h) x = V (ptX s h x) := by
  funext c
  have ha : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hr : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  simp only [cvec, utOf, smul_smul]
  rw [mul_div_assoc', mul_div_cancel_left₀ c ha, ← Complex.ofReal_mul, inv_mul_cancel₀ hr,
    Complex.ofReal_one, one_smul]

theorem ptSize_ptX (s : ℕ) (h : C.LPt) (x : ℂ) : D.ptSize (ptX s h x) = D.ptSize h + (s - 1) := by
  simp [D.ptSize, ptX]

theorem rd_pos (E : Type) [Field E] [NumberField E] : 0 < S6.rd E := by
  unfold S6.rd
  apply Real.rpow_pos_of_pos
  exact Int.cast_pos.mpr (abs_pos.mpr (NumberField.discr_ne_zero E))

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem dlB_ne_zero (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) (b s : ℕ) :
    KB.dlB S b s ≠ 0 := by
  have hrd := rd_pos E
  have hg0 : 0 < S.g := Nat.mul_pos hg1 hg2
  have hg : (0 : ℝ) < (S.g : ℝ) := by exact_mod_cast hg0
  unfold KB.dlB D.deG
  apply div_ne_zero (zpow_ne_zero _ hrd.ne')
  apply div_ne_zero two_ne_zero
  exact mul_ne_zero hrd.ne' (pow_ne_zero _ hg.ne')

structure FibreGerm (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (b s : ℕ) (a : List C.Letter) (Y : Finset C.LPt) where
  H : Type
  [nag : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  [cs : CompleteSpace H]
  V : C.LPt → ℂ → H
  bt : C.LPt → ℂ → H
  β : ℂ
  ε' : ℂ
  hβ : β ≠ 0
  hε' : ‖ε'‖ = 1
  hpsi : ∀ σ z : ℂ, G.psi β (σ * z) = KB.psiL S σ z
  measV : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → AEStronglyMeasurable (V (ptX s h x)) volume
  fibre : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 → ∀ c : ℂ, c ≠ 0 →
    KB.gN S v ε (b + s - 1) a (ptX s h x ++ [(1, c)]) (ptX s h' x' ++ [(1, c)]) =
      (KB.dlB S (b + s - 1) 1 : ℂ) * ⟪V (ptX s h x) c, V (ptX s h' x') c⟫_ℂ
  meas : ∀ h ∈ Y, StronglyMeasurable (bt h)
  loc : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖bz s (bt h) z‖ ^ 2) K
  germ : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
    ∀ᵐ D, D ∈ K → ‖utOf s V h x D - mainD s β ε' (bt h) x D‖ ≤ C * ‖x‖⁻¹
  dens : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ z : ℂ, z ≠ 0 →
    gDens S v ε b s a h h' z = (KB.dlB S b s : ℂ) * ⟪bz s (bt h) z, bz s (bt h') z⟫_ℂ

attribute [instance] FibreGerm.nag FibreGerm.ips FibreGerm.cs

def GermFibres (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s ≤ S.G.r + 2 → ∀ a, D.AdmAt S v a → ∀ Y : Finset C.LPt,
    (∀ h ∈ Y, D.ptSize h = b - 1) → Nonempty (FibreGerm S v ε b s a Y)

theorem integrable_of_decay {φ : ℂ → ℂ} (hφ : Continuous φ) {Cφ : ℝ}
    (h : ∀ c : ℂ, ‖φ c‖ ≤ Cφ * ((1 + ‖c‖) ^ 3)⁻¹) : Integrable φ := by
  have hg : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) := by
    apply integrable_one_add_norm
    rw [Complex.finrank_real_complex]
    norm_num
  have e : ∀ c : ℂ, (1 + ‖c‖) ^ (-(3 : ℝ)) = ((1 + ‖c‖) ^ 3)⁻¹ := fun c => by
    rw [Real.rpow_neg (by positivity)]
    norm_cast
  refine (hg.const_mul Cφ).mono' hφ.aestronglyMeasurable (ae_of_all _ fun c => ?_)
  rw [e]
  exact h c

def FibreGerm.toGermReal {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {ε : ℝ} {b s : ℕ} {a : List C.Letter}
    {Y : Finset C.LPt} (R : FibreGerm S v ε b s a Y) (hI : JC.ThmPIntPlace S v fun i => KB.dlB S i 1)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) (hε : 0 < ε) (hb : 1 ≤ b) (hs : 2 ≤ s) (hbs : b + s ≤ S.G.r + 2)
    (ha : D.AdmAt S v a) (hY : ∀ h ∈ Y, D.ptSize h = b - 1) : GermReal S v ε b s a Y := by
  classical

  have key : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 →
      Integrable (fun c => ⟪R.V (ptX s h x) c, R.V (ptX s h' x') c⟫_ℂ) ∧
      gK S v ε b s a (h, x) (h', x') = ∫ c, ⟪R.V (ptX s h x) c, R.V (ptX s h' x') c⟫_ℂ := by
    intro h hh h' hh' x x' hx hx'
    obtain ⟨w, hw⟩ := ha
    have hsz : D.ptSize (ptX s h x) = b + s - 1 - 1 := by rw [ptSize_ptX, hY h hh]; omega
    have hsz' : D.ptSize (ptX s h' x') = b + s - 1 - 1 := by rw [ptSize_ptX, hY h' hh']; omega
    obtain ⟨φ, hφc, hφeq, ⟨Cφ, hCφ⟩, hφint⟩ :=
      hI ε hε (b + s - 1) (by omega) (by omega) w (ptX s h x) (ptX s h' x') hsz hsz'
    have hdl : (KB.dlB S (b + s - 1) 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (dlB_ne_zero S hg1 hg2 _ _)
    have hpt : ∀ c : ℂ, c ≠ 0 → ⟪R.V (ptX s h x) c, R.V (ptX s h' x') c⟫_ℂ =
        (KB.dlB S (b + s - 1) 1 : ℂ)⁻¹ * (φ c / (S.sizeAt v a : ℂ)) := by
      intro c hc
      have hf := R.fibre h hh h' hh' x x' hx hx' c hc
      rw [hφeq c hc, hw]
      unfold KB.gN at hf
      rw [hf, ← mul_assoc, inv_mul_cancel₀ hdl, one_mul]
    have hae : (fun c => ⟪R.V (ptX s h x) c, R.V (ptX s h' x') c⟫_ℂ) =ᵐ[volume]
        fun c => (KB.dlB S (b + s - 1) 1 : ℂ)⁻¹ * (φ c / (S.sizeAt v a : ℂ)) := by
      filter_upwards [ae_ne_zero] with c hc using hpt c hc
    have hφI : Integrable φ := integrable_of_decay hφc hCφ
    refine ⟨((hφI.div_const _).const_mul _).congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, integral_const_mul, integral_div, hφint, hw]
    have e : b + s - 1 - 1 = b + s - 2 := by omega
    rw [e]
    unfold gK KB.gN
    simp only [ptX]
    rw [mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hdl, one_mul]
  have memV : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (R.V (ptX s h x)) 2 volume := by
    intro h hh x hx
    refine (memLp_two_iff_integrable_sq_norm (R.measV h hh x hx)).2 ?_
    have hi := (key h hh h hh x x hx hx).1
    refine hi.re.congr (Eventually.of_forall fun c => ?_)
    simp only
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  exact
    { H := R.H
      ut := utOf s R.V
      bt := R.bt
      β := R.β
      ε' := R.ε'
      hβ := R.hβ
      hε' := R.hε'
      hdl := dlB_ne_zero S hg1 hg2 b s
      hpsi := R.hpsi
      memU := fun h hh x hx => (memLp_cvec s (utOf s R.V h) x hx).2 (by rw [cvec_utOf s R.V h x hx]; exact memV h hh x hx)
      gram := fun h hh h' hh' x x' hx hx' => by
        rw [(key h hh h' hh' x x' hx hx').2]
        simp only [gramL, Uc]
        rw [cvec_utOf s R.V h x hx, cvec_utOf s R.V h' x' hx']
      meas := R.meas
      loc := R.loc
      germ := R.germ
      dens := R.dens }

theorem germLoc_of_fibres {S : C.HidaSetting E Wp Wq} {v : Fin S.f} (hI : JC.ThmPIntPlace S v fun i => KB.dlB S i 1)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) (hF : GermFibres S v) (hC : GermCont S v) : KB.GermLoc S v := by
  apply germLoc_of_realised _ hC
  intro ε hε b s hb hs hbs a ha Y hY
  obtain ⟨R⟩ := hF ε hε b s hb hs hbs a ha Y hY
  exact ⟨R.toGermReal hI hg1 hg2 hε hb hs hbs ha hY⟩

end loc

end

end Formalism.FourierDecayAlt.P.GermRealisation
end

section

open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def V0 (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) : Set (Mat k r) :=
  {x | 0 < Gf k r D.z D.z' x} ∩ ⋂ l ∈ L, {x | Dmin k r D.z D.z' x l ≠ 0}

lemma isOpen_big_cell_set (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) : IsOpen (V0 D L) := by
  unfold V0
  refine (isOpen_lt continuous_const (Gf_cont D.z D.z')).inter ?_
  refine isOpen_biInter_finset (fun l _ => ?_)
  exact isOpen_ne_fun (Dmin_cont D.z D.z' l) continuous_const

lemma mem_domL (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) (g : Mat k r) :
    g ∈ C6.domL D L ↔ g ∈ GV k r ∧ g ∈ V0 D L := by
  simp only [C6.domL, V0, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]

lemma domL_gpos {D : RealPlaceData k r Wp Wq} {L : Finset (Fin (r + 2))} {g : Mat k r} (hg : g ∈ C6.domL D L) :
    g ∈ GPos D := by
  exact ⟨hg.1, hg.2.1⟩

lemma nz_of_domL {D : RealPlaceData k r Wp Wq} {L : Finset (Fin (r + 2))} {g : Mat k r} (hg : g ∈ C6.domL D L)
    {nf : ℕ} {e : CT k r nf × List (Mat k r)} (he : Good L e) :
    (∀ l, (e.1.a l ≠ 0 ∨ e.1.b l ≠ 0) → Dmin k r D.z D.z' g l ≠ 0) ∧
      (e.1.c ≠ 0 → ((Gf k r D.z D.z' g : ℝ) : ℂ) ≠ 0) := by
  have hlast : Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0 := by
    intro h0
    have hG : 0 < Gf k r D.z D.z' g := hg.2.1
    simp only [Gf, h0, Complex.normSq_zero, zero_sub] at hG
    have := mul_nonneg (mul_pos D.T_pos D.T'_pos).le (Complex.normSq_nonneg (Dmin k r D.z D.z' g ⟨r, by omega⟩))
    linarith
  obtain ⟨hab, -, -⟩ := he
  refine ⟨fun l hl => ?_, fun _ => ?_⟩
  · rcases hab l hl with hl | rfl
    · exact hg.2.2 l hl
    · exact hlast
  · exact_mod_cast hg.2.1.ne'

lemma shape_flatMap' (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (Lf : FS k r nf) (f : CT k r nf × List (Mat k r) → FS k r nf) (g : Mat k r) :
    shape D fib F (Lf.flatMap f) g = (Lf.map fun e => shape D fib F (f e) g).sum := by
  induction Lf with
  | nil => simp [shape]
  | cons e Lf ih =>
    simp only [shape] at ih ⊢
    simp [ih, List.sum_append]

private lemma ckOn_rw_of_ckOn_add_length {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {UU : Set (Mat k r)}
    {f : Mat k r → E} : ∀ (w : List (Mat k r)) (n : ℕ∞), (∀ X ∈ w, inLie k r X) →
      CkOn (n + w.length) UU f → CkOn n UU (Rw w f) := by
  intro w
  induction w with
  | nil => intro n _ hf; simpa [Rw] using hf
  | cons X w ih =>
    intro n hw hf
    rw [Rw_cons']
    refine CkOn_Dx (x := (false, X)) (hw X (by simp)) (ih (n + 1) (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) ?_)
    have e : n + 1 + (w.length : ℕ∞) = n + ((X :: w).length : ℕ∞) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    rw [e]; exact hf

private lemma hasDerivAt_shape_crv_of_good (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {X : Mat k r} (hX : inLie k r X) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    ∀ Lf : FS k r nf, (∀ e ∈ Lf, Good L e) → (∀ e ∈ Lf, e.2.length + 1 ≤ m) →
      HasDerivAt (fun s => shape D fib F Lf (crv (false, X) g s)) (shape D fib F (step D X Lf) g) 0 := by
  intro Lf
  induction Lf with
  | nil =>
    intro _ _
    simp only [shape, step, List.map_nil, List.sum_nil, List.flatMap_nil]
    exact hasDerivAt_const _ _
  | cons e Lf ih =>
    intro hL hm
    have he : Good L e := hL e (by simp)
    have hgp := domL_gpos hg
    have hnz := nz_of_domL hg he
    have hcv := hasDerivAt_cv D fib hfib hX hgp e.1 hnz.1 hnz.2 he.2.1
    have hRw : CkOn 1 (GV k r) (Rw e.2 F) := by
      refine ckOn_rw_of_ckOn_add_length e.2 1 he.2.2 (sCkOn_mono ?_ hF)
      have := hm e (by simp)
      rw [add_comm]; exact_mod_cast this
    have hR : HasDerivAt (fun s => Rw e.2 F (crv (false, X) g s)) (Rw (X :: e.2) F g) 0 := by
      rw [Rw_cons']
      exact CkOn_diff (x := (false, X)) hX hRw hgp.1 hgp.1
    have hcv' := ((ContinuousLinearMap.restrictScalarsL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) ℝ ℝ).hasFDerivAt).comp_hasDerivAt
      (0 : ℝ) hcv
    have h1 := hcv'.clm_apply hR
    have h2 := ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he')) (fun e' he' => hm e' (List.mem_cons_of_mem _ he'))
    have h3 := h1.add h2
    show HasDerivAt (fun s => cv D fib e.1 (crv (false, X) g s) (Rw e.2 F (crv (false, X) g s)) +
      shape D fib F Lf (crv (false, X) g s)) _ 0
    refine h3.congr_deriv ?_
    rw [crv_zero]
    have hs : shape D fib F (step D X (e :: Lf)) g =
        shape D fib F (stepOne D X e) g + shape D fib F (step D X Lf) g := by
      simp only [step, shape_flatMap', List.map_cons, List.sum_cons]
    rw [hs]
    congr 1
    simp only [shape, stepOne, List.map_append, List.map_map, List.sum_append, Function.comp_def, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [← list_sum_apply, crv_zero]
    try rfl

theorem step_eq (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {X : Mat k r} (hX : inLie k r X) {Lf : FS k r nf}
    (hL : ∀ e ∈ Lf, Good L e) (hm : ∀ e ∈ Lf, e.2.length + 1 ≤ m) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    RdV X (shape D fib F Lf) g = shape D fib F (step D X Lf) g := by
  have hd := hasDerivAt_shape_crv_of_good D fib hfib L hF hX hg Lf hL hm
  rw [← hd.deriv]
  exact Dx_eq (false, X) (shape D fib F Lf) g

theorem expand (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) :
    ∀ (w : List (Mat k r)) (Lf : FS k r nf), (∀ X ∈ w, inLie k r X) → (∀ e ∈ Lf, Good L e) →
      (∀ e ∈ Lf, e.2.length + w.length ≤ m) → ∀ g ∈ C6.domL D L,
        Rw w (shape D fib F Lf) g = shape D fib F (steps D w Lf) g := by
  intro w
  induction w with
  | nil => intro Lf _ _ _ g _; rfl
  | cons X w ih =>
    intro Lf hw hL hm g hg
    have hX : inLie k r X := hw X (by simp)
    have hw' : ∀ Y ∈ w, inLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hm' : ∀ e ∈ Lf, e.2.length + w.length ≤ m := fun e he => by
      have := hm e he; simp only [List.length_cons] at this; omega
    have hev : (fun t : ℝ => Rw w (shape D fib F Lf) (crv (false, X) g t)) =ᶠ[𝓝 0]
        (fun t => shape D fib F (steps D w Lf) (crv (false, X) g t)) := by
      have hV : g ∈ V0 D L := ((mem_domL D L g).1 hg).2
      filter_upwards [crv_ev (x := (false, X)) (isOpen_big_cell_set D L) hV] with t ht
      exact ih Lf hw' hL hm' _ ((mem_domL D L _).2 ⟨crv_mem (x := (false, X)) hX hg.1 t, ht⟩)
    have hgood := good_steps D w hw' Lf hL
    have hstep := step_eq D fib hfib L hF hX (Lf := steps D w Lf) (fun e he => (hgood e he).1)
      (fun e he => by
        obtain ⟨-, e0, he0, hle⟩ := hgood e he
        have := hm e0 he0
        simp only [List.length_cons] at this
        omega) hg
    calc Rw (X :: w) (shape D fib F Lf) g
        = deriv (fun t : ℝ => Rw w (shape D fib F Lf) (crv (false, X) g t)) 0 := by
          rw [Rw_cons']; exact Dx_eq (false, X) _ g
      _ = deriv (fun t : ℝ => shape D fib F (steps D w Lf) (crv (false, X) g t)) 0 := hev.deriv_eq
      _ = RdV X (shape D fib F (steps D w Lf)) g := (Dx_eq (false, X) _ g).symm
      _ = shape D fib F (steps D (X :: w) Lf) g := hstep

end Formalism.FourierDecayAlt.P.MinorPolynomials
end
end
