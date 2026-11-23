module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovariantRepresentation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle013
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle126
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SemiTrace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tauE_star (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    tauE D τ (star x) = starRingEnd ℂ (tauE D τ x) :=
  D.sp.cm.cmUnram.2.1 _ x

theorem sum_two_re_tauE (D : D7) (e : D.host.E) :
    ∑ t, (((2 * (tauE D t e).re : ℝ)) : ℂ) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  classical
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (tauE D b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (tauE D a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, tauE D t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq] at h4
  rw [← h4, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.add_conj]

theorem re_xi_mul_sq (u : ℝ) (hu : 0 < u) :
    (Complex.I * ((u⁻¹ : ℝ) : ℂ) * ((1 + Complex.I * (u : ℂ)) / 2) ^ 2).re = -1 / 2 := by
  have h : Complex.I * ((u⁻¹ : ℝ) : ℂ) * ((1 + Complex.I * (u : ℂ)) / 2) ^ 2
      = ((-1 / 2 : ℝ) : ℂ) + Complex.I * (((1 - u ^ 2) / (4 * u) : ℝ) : ℂ) := by
    have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq, Complex.I_pow_three]
    ring
  rw [h]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

end GlobalTheory.SemiTrace

namespace GlobalTheory.SemiTrace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem alV_embH_eq_neg_one_zpow : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (y : Formalism.L2.Col.HomE D.host.E a b) (k : ℤ), (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T ((LinearMap.toMatrix' (y)).reindex (finCongr hT.symm) (finCongr hS.symm)) ((LinearMap.toMatrix' (y)).reindex (finCongr hT.symm) (finCongr hS.symm))) → alV D.host.d sc (embH (tauE D) δ y) = (-1 : ℂ) ^ k := by
  intro D ψ θ S T a b hS hT δ sc hP y k hk
  subst hS hT
  have hd : 0 < Real.sqrt D.host.d :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero))
  set M := (LinearMap.toMatrix' y).reindex (finCongr (rfl : T.rank = T.rank).symm) (finCongr (rfl : S.rank = S.rank).symm) with hMdef
  have hMij : ∀ i j, M i j = y (Pi.single j 1) i := by
    intro i j; simp [M, LinearMap.toMatrix'_apply]
  set s : D.what₂.Tau → ℝ := fun τ => ∑ i, ∑ j, Complex.normSq (tauE D τ (M i j)) with hs
  have hh : ∀ τ, tauE D τ (GlobalTheory.LatVac.hRat S T M M) = ((s τ : ℝ) : ℂ) := by
    intro τ

    simp only [GlobalTheory.LatVac.hRat, hP.gS, hP.gT, inv_one, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_sum, map_mul, tauE_star, hs]
    simp only [apply_ite (⇑(tauE D τ)), map_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul, tauE_star]
    push_cast
    rw [Finset.sum_comm]
    calc _ = ∑ j, ∑ i, ((Complex.normSq (tauE D τ (M i j)) : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.normSq_eq_conj_mul_self]
      _ = _ := Finset.sum_comm
  have hτ : ∀ τ, (tauE D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T M M)).re = -(s τ) / 2 := by
    intro τ
    rw [map_mul, map_mul, map_pow, map_div₀, map_add (f := _), map_one, map_ofNat, hh, hP.xi, Formalism.L2.Theta.tauE_sqrtMinusD,
      Complex.re_mul_ofReal, re_xi_mul_sq _ hd]
    ring
  have hk' : (k : ℂ) = ((-(∑ τ, s τ) : ℝ) : ℂ) := by
    have e1 := sum_two_re_tauE D (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T M M)
    rw [← hk] at e1
    push_cast at e1
    rw [← e1]
    simp only [hτ]
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  have hsc : sc * Complex.normSq δ = 2 * (Real.sqrt D.host.d)⁻¹ := by
    rw [← Complex.sq_norm]; exact hP.scale
  have hq : Formalism.L2.Th1.H.qOf (Real.sqrt D.host.d / 2) (HV sc) (embH (tauE D) δ y) = ∑ τ, s τ := by
    simp only [Formalism.L2.Th1.H.qOf, HV, LinearMap.mk₂'ₛₗ_apply, embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Complex.mul_conj]
    rw [show ((sc : ℂ) * ∑ x, ∑ x_1, ∑ x_2, ((Complex.normSq (δ * tauE D x (y (Pi.single x_2 1) x_1)) : ℝ) : ℂ)) =
        ((sc * ∑ x, ∑ x_1, ∑ x_2, Complex.normSq (δ * tauE D x (y (Pi.single x_2 1) x_1)) : ℝ) : ℂ) by push_cast; rfl,
      Complex.ofReal_re]
    simp_rw [Complex.normSq_mul, ← Finset.mul_sum]
    simp only [hs, hMij]
    rw [← mul_assoc sc, hsc]
    field_simp
  have hsum : ((∑ τ, s τ : ℝ) : ℂ) = -(k : ℂ) := by rw [hk']; push_cast; ring
  rw [alV, Formalism.L2.Th1.H.alphaQ, hq, hsum,
    show (Real.pi : ℂ) * Complex.I * -(k : ℂ) = ((-k : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I, _root_.zpow_neg, ← _root_.inv_zpow, inv_neg, inv_one]
end GlobalTheory.SemiTrace
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.PhCol

variable {D : D7}

theorem one_le_level (X : HidaSetting D) : 1 ≤ X.B.g := by
  rw [X.g_eq]
  exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem one_mem_level (X : HidaSetting D) : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
  refine ⟨(Formalism.UG.stabGL X.B.I.Lf).one_mem, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
  have h1 : X.B.I.fmat 1 = 1 := rfl
  rw [h1, sub_self, Matrix.zero_mulVec, smul_zero]

theorem psiInfU_of_mem_Hinf (X : HidaSetting D) (u : D.what₂.Word) (η : X.B.I.Ginf) (hη : η ∈ Hinf X u) :
    X.psiInfU u η = 1 := by
  have e := Formalism.L2.SG.PoincareInHH.Cut.psiInf_mul_H X u 1 η hη
  rw [one_mul] at e
  rw [e]
  exact Formalism.L2.SG.CovariantRepresentation.psiInfU_one X u

theorem castGA_mem_rat {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) :
    x ∈ I.GFset ↔ castGA e x ∈ I'.GFset := by
  subst e; rfl

theorem iotaX_mem_rat (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (g : GA D (D.sp.Y 0))
    (hg : g ∈ GQ (D.sp.Y 0)) : iotaX X h g ∈ X.B.I.GFset := by
  have e : iotaX X h g = castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D g) := rfl
  rw [e]
  exact (castGA_mem_rat h.symm _).1 ((Formalism.IndefR.RationalEmbedding.iota_rat D g).1 hg)

theorem Ph_of_dec (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (y : X.B.I.GA)
    (n : X.B.I.Gf) (hh : Hfin X u) (k : X.B.I.Gf) (hd : IsDec X u y.2 n hh k) :
    Ph X u hK T y = phVal X u hK T y.1 n hh k := by
  have hex : ∃ n h k, IsDec X u y.2 n h k := ⟨n, hh, k, hd⟩
  unfold Ph
  rw [dite_eq_left hex]
  exact Formalism.L2.SG.Pf.phWellDef_holds X u T y.1 y.2 _ n _ k _ hh hex.choose_spec.choose_spec.choose_spec hd

variable {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D}

theorem continuous_toH (B : SBes X h u ψ A) : Continuous B.toH := by
  have he : Continuous (embA B.d B.o) := by
    have e : (embA B.d B.o : GA D A → GA D (D.sp.Y 0)) = fun a => B.d.emb0 (B.o.emb (a, 1)) := rfl
    rw [e]
    exact B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  have hc : Continuous fun a => iotaX X h (embA B.d B.o a) := (iotaX X h).continuous.comp he
  unfold SBes.toH
  exact (hc.fst.subtype_mk _).prodMk (hc.snd.subtype_mk _)

theorem continuous_col (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (ξ : X.Vpi u) :
    Continuous fun p : Hinf X u × Hfin X u => (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ p := by
  obtain ⟨hT1, hT2⟩ := T.2
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  rw [continuous_iff_continuousAt]
  intro p0
  have hπ : Continuous fun η : Hinf X u => X.piU u η ξ :=
    ((X.piU_rep u).2.2.2.2 ξ).comp_continuous continuous_subtype_val (fun η => hinf_le_sinf X u _ η.2)
  let L : X.Vpi u →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : Hinf X u × Hfin X u => ℂ) ((1 : Hinf X u), p0.2)).comp
      (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ))
  have hG : Continuous fun p : Hinf X u × Hfin X u => L (X.piU u p.1 ξ) :=
    L.continuous_of_finiteDimensional.comp (hπ.comp continuous_fst)
  have hUo : IsOpen {p : Hinf X u × Hfin X u |
      (X.xu u)⁻¹ * ((p0.2⁻¹ * p.2 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g} := by
    refine (X.B.I.topf_open X.B.g (one_le_level X)).preimage ?_
    exact (continuous_const.mul (continuous_subtype_val.comp (continuous_const.mul continuous_snd))).mul
      continuous_const
  have hp0 : p0 ∈ {p : Hinf X u × Hfin X u |
      (X.xu u)⁻¹ * ((p0.2⁻¹ * p.2 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g} := by
    show (X.xu u)⁻¹ * ((p0.2⁻¹ * p0.2 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g
    rw [inv_mul_cancel]
    simpa using one_mem_level X
  refine hG.continuousAt.congr (Filter.eventually_of_mem (hUo.mem_nhds hp0) fun p hp => ?_)
  obtain ⟨η, k⟩ := p
  have hp' : (X.xu u)⁻¹ * ((p0.2⁻¹ * k : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g := hp
  obtain ⟨hK2, hχ⟩ := hL.1 _ hp'
  let κ : Ku X u hK := ⟨p0.2⁻¹ * k, hK2⟩
  have e1 : ((η, k) : Hinf X u × Hfin X u) = (η, p0.2) * (1, ((κ : Hfin X u))) := by
    ext
    · simp
    · simp [κ]
  have e2 : ((η, p0.2) : Hinf X u × Hfin X u) = (1, p0.2) * (η, 1) := by
    ext <;> simp
  have hψ : ((psiK X u hK κ : ℂˣ) : ℂ) = 1 := hχ
  show L (X.piU u η ξ) = (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (η, k)
  rw [e1, (hT1 ξ).2 (η, p0.2) κ, hψ, one_mul, e2, ← hT2 η ξ (1, p0.2)]
  rfl

end GlobalTheory.Core.Mi.PhCol

namespace GlobalTheory.Core.Mi.PhCol

theorem ph_colForm : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK),
    (∀ ξ, IsContAut A (B.colForm T.1 ξ)) ∧ ∀ n ∈ flagN B.d, ∀ (a : GA D A) (y : X.B.I.Ginf),
      Ph X u hK T (iotaX X h (n * embA B.d B.o a) * (y, X.xu u)) =
        star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) * B.colForm T.1 (X.Wu u y) a := by
  intro D X h u ψ A B hK T
  obtain ⟨hT1, hT2⟩ := T.2
  refine ⟨fun ξ => ⟨fun γ hγ g => ?_, ?_⟩, fun n hn a y => ?_⟩
  ·
    have hrat : embA B.d B.o γ ∈ GQ (D.sp.Y 0) := by
      have e : embA B.d B.o γ = B.d.emb0 (B.o.emb (γ, 1)) := rfl
      rw [e]
      exact B.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (B.o.emb_mem_GQ hγ (one_mem _))
    have hr := iotaX_mem_rat X h _ hrat
    have hH := (B.tieH (embA B.d B.o γ)).1 ⟨γ, rfl⟩
    let γ' : Gam X u := ⟨iotaX X h (embA B.d B.o γ), Subgroup.mem_inf.2 ⟨hr, Subgroup.mem_prod.2 hH⟩⟩
    have e : B.toH (γ * g) = (iotaI X u γ', iotaF X u γ') * B.toH g := by
      refine Prod.ext ?_ ?_ <;> apply Subtype.ext
      · show (iotaX X h (embA B.d B.o (γ * g))).1 = (iotaX X h (embA B.d B.o γ)).1 * (iotaX X h (embA B.d B.o g)).1
        rw [map_mul, map_mul, Prod.fst_mul]
      · show (iotaX X h (embA B.d B.o (γ * g))).2 = (iotaX X h (embA B.d B.o γ)).2 * (iotaX X h (embA B.d B.o g)).2
        rw [map_mul, map_mul, Prod.snd_mul]
    show (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (B.toH (γ * g)) =
      (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (B.toH g)
    rw [e]
    exact (hT1 ξ).1 γ' (B.toH g)
  ·
    exact (continuous_col hK T ξ).comp (continuous_toH B)
  ·
    obtain ⟨hn1, hn2⟩ := (B.tieN n).1 hn
    obtain ⟨ha1, ha2⟩ := (B.tieH (embA B.d B.o a)).1 ⟨a, rfl⟩
    set m := iotaX X h n with hm
    set b := iotaX X h (embA B.d B.o a) with hb
    have e : iotaX X h (n * embA B.d B.o a) * (y, X.xu u) = (m.1 * b.1 * y, m.2 * b.2 * X.xu u * 1) := by
      rw [map_mul, ← hm, ← hb]
      ext <;> simp [mul_assoc]
    have hd : IsDec X u (m.1 * b.1 * y, m.2 * b.2 * X.xu u * 1).2 m.2 ⟨b.2, ha2⟩ 1 :=
      ⟨hn2, one_mem_level_subgroup X, rfl⟩
    rw [e, Ph_of_dec X u hK T _ _ _ _ hd]
    unfold phVal
    have hm1S : m.1 ∈ X.SinfU u := fun v => (hn1 v).1
    have hb1S : b.1 ∈ X.SinfU u := hinf_le_sinf X u _ ha1
    have hW : X.Wu u (m.1 * b.1 * y) = X.psiInfU u m.1 • X.piU u b.1 (X.Wu u y) := by
      rw [mul_assoc, (X.Wu_spec u).1 m.1 hm1S, (X.piU_rep u).2.2.2.1 m.1 hn1, ContinuousLinearMap.one_apply,
        (X.Wu_spec u).1 b.1 hb1S]
      have hpsi : X.psiInfU u b.1 = 1 := psiInfU_of_mem_Hinf X u b.1 ha1
      change X.psiInfU u m.1 • (X.psiInfU u b.1 • X.piU u b.1 (X.Wu u y)) = _
      rw [hpsi, one_smul]
    have hC : (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.piU u b.1 (X.Wu u y)) (1, ⟨b.2, ha2⟩) =
        B.colForm T.1 (X.Wu u y) a := by
      have := hT2 ⟨b.1, ha1⟩ (X.Wu u y) (1, ⟨b.2, ha2⟩)
      refine this.trans ?_
      show (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y) ((1, ⟨b.2, ha2⟩) * (⟨b.1, ha1⟩, 1)) =
        (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y) (B.toH a)
      refine congrArg ((T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y)) ?_
      refine Prod.ext ?_ ?_ <;> apply Subtype.ext
      · show (1 : X.B.I.Ginf) * b.1 = (iotaX X h (embA B.d B.o a)).1
        rw [one_mul]
      · show b.2 * (1 : X.B.I.Gf) = (iotaX X h (embA B.d B.o a)).2
        rw [mul_one]
    rw [hW, map_smul, Pi.smul_apply, smul_eq_mul, hC, chi2_apply_one X hK, B.tieψ n hn]
    ring

end GlobalTheory.Core.Mi.PhCol
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.MainNotions.StandardLattice

namespace GlobalTheory.Core.Mi.SeeReal

variable {D : D7}

theorem isAtTau_atTau (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    IsAtTau θ V τ g (atTau θ V τ g) := by
  have hex := (Formalism.IndefR.Eqv.atTauExUnique_holds D θ hθ V τ g hg).exists
  unfold atTau
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem eq_of_conj {n : ℕ} {P A B : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P.det) (e : P * A * P⁻¹ = B) :
    A = P⁻¹ * B * P := by
  rw [← e]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul P hP, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left P A hP]

theorem phi_inst (v : InfinitePlace D.host.F) (x : D.host.E) :
    (Formalism.IndefR.RationalEmbedding.inst D).φ v x = embS D ((Formalism.L2.Host.tauPl D).symm v) x := rfl

theorem realSplit_gen {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hιE : ∀ x : I.E, HEq (ιE x) x) (pl : InfinitePlace I.F ≃ D.what₂.Tau)
    (hφ : ∀ v (x : I.E), I.φ v x = embS D (pl v) (ιE x)) (θ : InfFam D) (hθ : IsInfFam θ) :
    (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) k).1 = 1) ∧
    (∀ k : GA D (D.sp.Y 0), k ∈ GinfC (D.sp.Y 0) ↔ ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) k).2 = 1) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ),
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).2 = 1 ∧
      (∀ v, v ≠ pl.symm τ → ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).1 v = 1) ∧
      HEq (uMat (((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ)))
        ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm)
          ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧
    ∀ τ (y : Formalism.REAL.UJ (I.ε (pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ),
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ) = y := by
  subst h
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hι : ∀ x, ιE x = x := fun x => eq_of_heq (hιE x)
  have key : ∀ τ τ' : D.what₂.Tau, embS D τ = embS D τ' → τ = τ' :=
    fun τ τ' e => D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 e))
  have hpl : pl = (Formalism.L2.Host.tauPl D).symm := Equiv.ext fun v => key _ _ (RingHom.ext fun x => by
    have e := hφ v x
    have e2 : embS D (pl v) (ιE x) = embS D (pl v) x := congrArg _ (hι x)
    exact (e2.symm.trans e.symm).trans (phi_inst v x))
  subst hpl
  have hT : ∀ k, ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)) k =
      Formalism.IndefR.RationalEmbedding.iota D k := fun _ => rfl
  have hP : ∀ v, IsUnit ((Formalism.IndefR.RationalEmbedding.inst D).P v).det :=
    fun v => (Matrix.isUnit_iff_isUnit_det _).mp ((Formalism.IndefR.RationalEmbedding.inst D).P_unit v)
  refine ⟨fun k => ?_, fun k => ?_, fun τ g hg => ?_, fun τ y => ?_⟩
  · rw [hT]
    have e := Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (Formalism.IndefR.RationalEmbedding.iota D k)
    rwa [ContinuousMulEquiv.symm_apply_apply] at e
  · rw [hT]
    have e := Formalism.L2.SG.EvalTIota.iota_symm_mem_GinfC (Formalism.IndefR.RationalEmbedding.iota D k)
    rwa [ContinuousMulEquiv.symm_apply_apply] at e
  · have hg' : gᴴ * gramAt D (D.sp.Y 0) τ * g = gramAt D (D.sp.Y 0) τ := hg
    have hk := isAtTau_atTau (Formalism.IndefR.Eqv.thetaC D) (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g hg'
    rw [hT]
    generalize atTau (Formalism.IndefR.Eqv.thetaC D) (D.sp.Y 0) τ g = k at hk ⊢
    obtain ⟨x, rfl⟩ := (Formalism.IndefR.RationalEmbedding.iota D).symm.surjective k
    rw [ContinuousMulEquiv.apply_symm_apply]
    have hbr := Formalism.L2.SG.EvalTIota.infMat_brg_i x
    refine ⟨(Formalism.L2.SG.EvalTIota.iota_symm_mem_GinfC x).1 hk.1, fun v hv => ?_, heq_of_eq ?_⟩
    · obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
      have hρ : ρ ≠ τ := fun e => hv (by rw [e]; rfl)
      have e0 : Formalism.L2.SG.EvalTIota.Pi (Formalism.L2.Host.tauPl D ρ) * Formalism.L2.SG.EvalTIota.uM' x (Formalism.L2.Host.tauPl D ρ) *
          (Formalism.L2.SG.EvalTIota.Pi (Formalism.L2.Host.tauPl D ρ))⁻¹ = (1 : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ) := by
        rw [← hbr ρ, hk.2.2 ρ hρ]
      have e1 := eq_of_conj (hP _) e0
      simp only [Formalism.L2.SG.EvalTIota.Pi, Formalism.L2.SG.EvalTIota.uM'] at e1
      have e2 : uMat (x.1 (Formalism.L2.Host.tauPl D ρ)) = 1 := by
        rw [e1]
        erw [Matrix.mul_one]
        exact Matrix.nonsing_inv_mul _ (hP _)
      exact Subtype.ext (Units.ext e2)
    · exact eq_of_conj (hP _) ((hbr τ).symm.trans hk.2.1)
  · classical
    let x0 : (Formalism.IndefR.RationalEmbedding.inst D).GA :=
      (Pi.mulSingle (M := fun v => Formalism.REAL.UJ ((Formalism.IndefR.RationalEmbedding.inst D).ε v)) (Formalism.L2.Host.tauPl D τ) y, 1)
    have hbr := Formalism.L2.SG.EvalTIota.infMat_brg_i x0
    let g : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ :=
      (Formalism.IndefR.RationalEmbedding.inst D).P (Formalism.L2.Host.tauPl D τ) * uMat y * ((Formalism.IndefR.RationalEmbedding.inst D).P (Formalism.L2.Host.tauPl D τ))⁻¹
    have hk0 : IsAtTau (Formalism.IndefR.Eqv.thetaC D) (D.sp.Y 0) τ g ((Formalism.IndefR.RationalEmbedding.iota D).symm x0) := by
      refine ⟨(Formalism.L2.SG.EvalTIota.iota_symm_mem_GinfC x0).2 rfl, ?_, fun ρ hρ => ?_⟩
      · rw [hbr τ]
        have hy : x0.1 (Formalism.L2.Host.tauPl D τ) = y :=
          Pi.mulSingle_eq_same (M := fun v => Formalism.REAL.UJ ((Formalism.IndefR.RationalEmbedding.inst D).ε v)) (Formalism.L2.Host.tauPl D τ) y
        have hy' : Formalism.L2.SG.EvalTIota.uM' x0 (Formalism.L2.Host.tauPl D τ) = uMat y := by
          show uMat (x0.1 (Formalism.L2.Host.tauPl D τ)) = uMat y
          rw [hy]
        rw [hy']
        rfl
      · rw [hbr ρ]
        have hne : Formalism.L2.Host.tauPl D ρ ≠ Formalism.L2.Host.tauPl D τ := (Formalism.L2.Host.tauPl D).injective.ne hρ
        have h1 : x0.1 (Formalism.L2.Host.tauPl D ρ) = 1 := Pi.mulSingle_eq_of_ne hne _
        have h1' : Formalism.L2.SG.EvalTIota.uM' x0 (Formalism.L2.Host.tauPl D ρ) = 1 := by
          show uMat (x0.1 (Formalism.L2.Host.tauPl D ρ)) = 1
          rw [h1]
          rfl
        rw [h1']
        erw [Matrix.mul_one]
        exact Matrix.mul_nonsing_inv _ (hP _)
    have hgU : gᴴ * gramAt D (D.sp.Y 0) τ * g = gramAt D (D.sp.Y 0) τ :=
      Formalism.IndefR.Eqv.atTauUnitary_holds D _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g _ hk0
    refine ⟨g, hgU, ?_⟩
    have hu := (Formalism.IndefR.Eqv.atTauExUnique_holds D _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g hgU).unique
      (isAtTau_atTau _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g hgU) hk0
    rw [hT, hu, ContinuousMulEquiv.apply_symm_apply]
    exact Pi.mulSingle_eq_same (M := fun v => Formalism.REAL.UJ ((Formalism.IndefR.RationalEmbedding.inst D).ε v)) _ _

theorem realSplit_of_idE : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (θ : InfFam D), IsInfFam θ → IdE X → RealSplit X h θ :=
  fun _ X h θ hθ hE => realSplit_gen h X.ιE hE X.pl X.φ_eq θ hθ

end GlobalTheory.Core.Mi.SeeReal
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param : ∀ (D : D7) (V : HSp D), CoCpt V → ∀ (v : Vol V) (P : Type) [TopologicalSpace P] (K : GA D V → P → ℂ), Continuous (Function.uncurry K) → (∀ γ ∈ GQ V, ∀ g p, K (γ * g) p = K g p) → (∀ p, IntegrableOn (fun g => K g p) v.𝓕 v.μ) ∧ (Continuous fun p => ∫ g in v.𝓕, K g p ∂v.μ) ∧ ∀ p₀, ∃ C : ℝ, ∀ᶠ p in nhds p₀, ∀ g, ‖K g p‖ ≤ C := by
  first | exact @GlobalTheory.CocompactParam.continuous_integral_param | exact GlobalTheory.CocompactParam.continuous_integral_param | (intros; apply GlobalTheory.CocompactParam.continuous_integral_param <;> assumption)
end
