module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Formalism.LocalRingCardinality.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle410
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle312
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle203
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle263
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle426
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle415
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle340
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle416
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle386
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle422
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle207
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle229
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle104
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle154
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle077
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle401
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle423
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle385
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle394
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle391
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle138
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle370
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle424
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle425
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
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.OpenCellNorm

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (t : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (t • A) = ‖t‖ ^ 2 * hsNormSq A := by
  have h : hsInner (t • A) (t • A) = ((‖t‖ ^ 2 : ℝ) : ℂ) * hsInner A A := by
    simp only [hsInner, Finset.mul_sum, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hsNormSq, h, Complex.re_ofReal_mul, hsNormSq]

theorem bigCell_mem_of_weight {k r : ℕ} (hk : 2 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ}
    {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : IsSection k r z z' μsec) {q : (Fin r → ℂ) × ℂ}
    (hq : bcWeight k r (Tz k r z) (Tz k r z') q ≠ 0) : bigCell k r q.1 (μsec q.2) ∈ UH (Hpk k r) := by
  unfold bcWeight at hq
  split_ifs at hq with h
  · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hq
    refine GlobalTheory.bigCell_mem_unitary k r _ _ (fun a ha => ?_) (hs.2 _ (lt_of_le_of_ne h fun e => ?_)).1
    · refine Finset.prod_ne_zero_iff.1 h1 a (Finset.mem_univ a) ?_
      rw [ha, norm_zero]
      exact zero_pow (by unfold Mdim; omega)
    · rw [e, sub_self] at h2
      exact h2 (zero_pow (by omega))
  · exact absurd rfl hq

theorem lintegral_weight_smul {k r : ℕ} (hk : 2 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ}
    {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : IsSection k r z z' μsec)
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {J J' : MatKR k r → (Wq →L[ℂ] Wp)} {η : ℂ} (h : ∀ γ ∈ UH (Hpk k r), J γ = η • J' γ) :
    ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q *
        hsNormSq (J (bigCell k r q.1 (μsec q.2)))) =
      ENNReal.ofReal (‖η‖ ^ 2) * ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q *
        hsNormSq (J' (bigCell k r q.1 (μsec q.2)))) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  by_cases hq : bcWeight k r (Tz k r z) (Tz k r z') q = 0
  · simp [hq]
  · rw [h _ (bigCell_mem_of_weight hk hs hq), hsNormSq_smul, ← ENNReal.ofReal_mul (sq_nonneg _), mul_left_comm]

theorem exists_bessel_scale (hH : Hyps) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)}
    {u : ℕ → ℝ} {c : ℂ} {μW μN μG νq : Measure (Mt k r)} (hc : c ≠ 0) (hS : SideG k r z π u μW μN μG νq)
    {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ} (R : Rep k r) (hR : R.IsDS ε mu)
    (hU : Formalism.MainNotions.S.IsURepOn (GG k r) R.σ) (hg : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) :
    ∃ l : R.H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π l ∧
      ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x) := by
  obtain ⟨t, ht, hN, hz, -⟩ := GlobalTheory.T.exists_unitaryTorus_scale_besselCharacter k r c hc
  obtain ⟨-, hW, hψ⟩ := hz z hS.1
  obtain ⟨hS', hm⟩ := GlobalTheory.T.torus_normaliser_bessel hH k r Wp z π u c μW μN μG νq t ht hN hW hψ hS
  obtain ⟨l₁, hl⟩ := GlobalTheory.exists_normalised_bessel_map hH k r ε mu h R Wp _ _ _ _ _ _ _ hR hg hok hS'
  obtain ⟨h1, h2⟩ := hm R hU
  refine ⟨fun v => l₁ (R.σ t⁻¹ v), (h1 _).2 ?_, h2 l₁ hl⟩
  have e : (fun v => l₁ (R.σ t⁻¹ (R.σ t v))) = l₁ := by
    funext v
    have h3 := hU.1.2 _ (PI.HwUniqW.inv_mem_UH ht) _ ht
    rw [show t⁻¹ * t = 1 from PI.HwUniqW.inv_mul_UH' ht, hU.1.1] at h3
    exact congrArg l₁ (congrArg (fun T : R.H →L[ℂ] R.H => T v) h3).symm
  show IsBes R z π (fun v => l₁ (R.σ t⁻¹ (R.σ t v)))
  rw [e]
  exact hl.1

theorem norm_eq_const_div_deg : Hyps → AmpKF → CellConv → ∀ Cg cb Cu cT CT C0 C1 Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → cdScaleTie D → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W → ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec → ∃ K : ℝ, 0 < K ∧ ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A → MMv D w w' A μsec = ENNReal.ofReal (K / A.deg) := by
  intro hH hKF hCC Cg cb Cu cT CT C0 C1 Cn
  refine ⟨Cn, fun D large₂ C' Cl hCl hBig hcd hZ τ w w' hTT θ hθw W hW μsec hsec => ?_⟩
  by_cases hex : ∃ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A
  swap
  · exact ⟨1, one_pos, fun lam' _ A hA => absurd ⟨lam', A, hA⟩ hex⟩
  obtain ⟨lam₀, A₀, hA₀⟩ := hex
  haveI := FiniteDimensional.complete ℂ W.Wp
  haveI := FiniteDimensional.complete ℂ W.Wq
  have hθ : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos (Real.exp_pos _) _) hθw.1
  have hv1 : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv : 0 < D.host.v := by linarith
  have hka : 0 < D.host.ka := div_pos Real.pi_pos hv
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  have hkg : 0 < D.host.ka / gg D := div_pos hka (mul_pos hg0 hg1)
  have hc : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by positivity)
  have hT : 0 < Tr D w := by unfold Tr; exact_mod_cast hTT.1.pos
  have hT' : 0 < Tr D w' := by unfold Tr; exact_mod_cast hTT.2.1.pos
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hκN : kapN D θ ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  obtain ⟨-, -, -, o1, o2⟩ := GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W lam₀ A₀ hθ hv hTT hW hA₀
  have n1' : 0 < Module.finrank ℂ W.Wp := by haveI := o1.2.2.1; exact Module.finrank_pos
  have n2' : 0 < Module.finrank ℂ W.Wq := by haveI := o2.2.2.1; exact Module.finrank_pos
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := o1.2.2.2.2.2.2.2.2.1
  obtain ⟨κ, hκ, hdeg⟩ := GlobalTheory.T.formal_degree_proportional hH D τ w w' θ W hcd hW
  obtain ⟨c, hc0, hnorm⟩ := GlobalTheory.T.uniform_bessel_constant hH hKF hCC _ _ (toBessel D τ w w' θ W lam₀ A₀ hW hA₀ hT hT') W.μG μsec hk hc
    hκN ENNReal.ofReal_ne_top hW.2.2.2.2.2.2.1 hsec
  have hW' := hW
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, -, w2, -, hN, q1, q2⟩ := hW'
  let sq : (Fin D.R.k → ℝ) → ℕ → ℝ := fun u n => if h : n - 1 < D.R.k then u ⟨n - 1, h⟩ else 0
  have hsq : ∀ u (i : Fin D.R.k), sq u (i.val + 1) = u i := fun u i => by simp [sq]
  have s1 : SideG D.R.k D.R.rS W.z W.π (sq (uS D w τ)) W.μW W.μN W.μG W.νS :=
    ⟨z1, t1 ▸ hT, ⟨_, c1⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ _ _ _ z1 (t1 ▸ hT) c1 (hsq _), w1, hNH, hG, q1⟩
  have s2 : SideG D.R.k D.R.rS W.z' W.π' (sq (uS D w' τ)) W.μW' W.μN W.μG W.νS' :=
    ⟨z2, t2 ▸ hT', ⟨_, c2⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ _ _ _ z2 (t2 ▸ hT') c2 (hsq _), w2, hNH, hG, q2⟩
  obtain ⟨hNum, hcell, heps⟩ := GlobalTheory.T.momentPieriNumerics_of_sizeHyps D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w _ (hsq _)
  obtain ⟨⟨-, -, -, -, hok⟩, hν⟩ := GlobalTheory.NumFam.num_fam _ _ _ _ _ _ _ _ _ hNum
  refine ⟨c * κ * (Module.finrank ℂ W.Wp * Module.finrank ℂ W.Wq), by positivity, fun lam' hl A hA => ?_⟩
  obtain ⟨ν, hlam, hn1, -⟩ := GlobalTheory.hcParam_sub_integral _ (lamD D τ) lam' hNum.2.1 hA.1
  have hq : n1 ν ≤ D.R.k * D.R.m ^ 5 := by
    have hm : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
    have h1 : Cn ≤ (D.R.m : ℝ) ^ 2 := by have := hBig.2.2; nlinarith
    have h2 : ((n1 ν : ℕ) : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 5 := by
      rw [hn1]
      calc _ ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := hl
        _ ≤ (D.R.m : ℝ) ^ 2 * D.R.k * (D.R.m : ℝ) ^ 3 := by gcongr
        _ = _ := by ring
    exact_mod_cast h2
  have hgap : GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) := by
    rw [hlam, ← heps]; exact (hν ν hq).2.2.1
  have hDS : (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).IsDS (epsSH D.R) lam' := ⟨hA.1, hA.2.1⟩
  have hU := (GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W lam' A hθ hv hTT hW hA).1
  obtain ⟨l, b1, e1⟩ := exists_bessel_scale hH hc s1 ⟨A.H, A.σ⟩ hDS hU hgap hok
  obtain ⟨l', b2, e2⟩ := exists_bessel_scale hH hc s2 ⟨A.H, A.σ⟩ hDS hU hgap hok
  obtain ⟨k1, k2, w0, η, hw0, hη, hJ⟩ :=
    GlobalTheory.T.bessel_period_positivity hH D τ w w' θ W lam' A _ l l' hθ hkg hT hT' hW hA hgap hok b1 b2 e1 e2
  have hw0' : w0 ≠ 0 := by
    obtain ⟨P, -, h1, -⟩ := hw0
    rintro rfl
    simp at h1
  obtain ⟨d1, d2⟩ := hdeg lam' A hA w0 hw0'
  have hd : 0 < PI.BesselPeriodGGP.fdegH W.μG A.σ w0 := by
    rw [d1] at d2; exact (mul_pos_iff_of_pos_left hκ).1 d2
  rw [hN] at e1 e2
  have key := hnorm ⟨A.H, A.σ⟩ lam' _ l l' w0 hDS hgap hok hcell e1 e2 k1 k2 hw0
  have h5 := lintegral_weight_smul hk hsec (J := A.J W.μG)
    (J' := amp (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) l l' w0 W.μG) (η := η) fun γ hγ => hJ W.μG γ hγ hG.2.2.1
  unfold MMv
  rw [← t1, ← t2, h5]
  refine (congrArg _ key).trans ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _), hη, mul_pow, Real.sq_sqrt (by positivity), d1]
  congr 1
  show _ * (c / PI.BesselPeriodGGP.fdegH W.μG A.σ w0 ^ 3) = _
  field_simp

end GlobalTheory.Amp.OpenCellNorm
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDictCore_holds : ∀ D : D7, ColDictCore D := by
  intro D
  unfold ColDictCore
  intro X u F Tr hK hLev hStab

  have hConj : ∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a) :=
    GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X Tr.ιA ⟨Tr.ιA_rat, Tr.ιA_int⟩
  refine ⟨(GlobalTheory.T.transport_represents_classes_weight_one D X u F Tr hK hConj hLev).1, GlobalTheory.T.columnDictionary_into_stepZeroForms D X u F Tr hK hConj hLev,
    GlobalTheory.T.columnDictionary_bijective_of_levelMatch D X u F Tr hK hConj hLev, ?_⟩
  intro what₂ cs hinj hReps
  exact GlobalTheory.T.columnDictionary_isometric_of_representatives D X u F Tr hK hConj hLev hStab what₂ cs hinj hReps

end GlobalTheory.St
end

section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HL

namespace GlobalTheory.Unfold

private theorem isFullLattice_of_local_span {D : D7} (Z : LocDat D) (p : PlF D) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ)
    (hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤) :
    Submodule.IsFullLattice D.host.E Λ := by
  let U := Submodule.span D.host.E (Λ : Set (VS D).V)
  let b := Module.finBasis D.host.E U
  let W := Submodule.span (D.s.atP p).Ep
    (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
  have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
    have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
    change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
    rw [map_sum, map_sum] at hx
    rw [← hx]
    exact W.sum_mem fun i _ => by
      rw [map_smul, baseChange_smul₂]
      exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  have htop : W = ⊤ := by
    apply top_le_iff.mp
    rw [← hspan, lattice₂, Submodule.span_span_of_tower]
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, heq⟩
    rw [← heq]
    exact hW ⟨x, Submodule.subset_span hx⟩
  refine { toIsLattice := hΛ, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
  rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
  simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
    finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)

theorem mass_genus_local_weights : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ d0 : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ₀}.Finite) → ∃ V1 : ℝ, 0 < V1 ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → {p | d p ≠ d0 p}.Finite → massA F F' d = ENNReal.ofReal (V1 * ∏ᶠ p, LocNG.Datum.wt (d0 p) (d p)) := by
  intro D X Y u u' F F' w hw hG Z FP hB hR d0 hd0 hΛ
  obtain ⟨φ, hφi, hφE⟩ := GlobalTheory.T.frameFixingIsometries_embed_prod_localUnitary D X Y u u' F F' w hw hG Z FP hB hR
  obtain ⟨Λ₀, hLO⟩ := GlobalTheory.T.exists_globalLattice_over_localInnerData D Z FP d0 hd0 hΛ
  have hrk : ∀ p : PlF D, Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    intro p
    have hm : D.R.m = 2 * D.R.rS + 2 := by
      have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; unfold Ranks.rS; omega
    rw [finrank_Vp]; unfold Ranks.r; omega
  have hact : ∀ p : PlF D, ∃ act : MulAction ↥(FP p).UW0 (LocNG.Datum (FP p)),
      (∀ (g : ↥(FP p).UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧
      ∀ d (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d :=
    fun p => GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (hrk p) (hR p)
  choose act hMv hSt using hact
  letI : ∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p)) := act
  have hMv' : ∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d' := hMv
  have hSt' : ∀ p (d : LocNG.Datum (FP p)) (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ g • d = d := hSt
  obtain ⟨hc0, hfin, hdd⟩ := GlobalTheory.T.localLatticeStabilisers_commensurable_almostEverywhere D X Y u u' F F' w hw hG Z FP hB hR hMv' hSt' Λ₀ d0 hLO
  have hlat : Submodule.IsLattice D.host.E Λ₀ := hLO.1
  have hfull : Submodule.IsFullLattice D.host.E Λ₀ := by
    obtain ⟨p⟩ := GlobalTheory.PhiEmbed.exists_place D
    obtain ⟨τ, hτ, heq⟩ := hLO.2 p
    apply isFullLattice_of_local_span Z p Λ₀ hlat
    rw [← heq]
    exact (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (d0 p) τ hτ).2
  obtain ⟨V1, hV1, hmain⟩ := GlobalTheory.T.mass_genus_restricted_product (fun p => ↥(FP p).UW0) (fun p => LocNG.Datum (FP p))
    (fun p => (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype) ↥(FlagPairStabilizer F F') φ hφi
    (GlobalTheory.T.frameFixingIsometry_ext_preserves_completions_ae D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀ hfull)
    (GlobalTheory.T.finite_doubleCosets_rational_localLatticeStabilizers D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀
      (by first | exact hfull | exact hfull.toIsLattice))
    (GlobalTheory.T.finite_rationalIsometries_fixing_frames_conjStabilizer D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀ hfull) d0 hc0 hfin
  refine ⟨V1, hV1, fun d hd hfd => ?_⟩
  have h3 := hdd d hd
  rw [GlobalTheory.T.genusMass_eq_sum_over_rationalGroup_orbits D X Y u u' F F' w hw hG Z FP hB hR φ hφE hφi hMv' d]
  have hm2 := hmain d (fun p => ⟨(h3 p).1, (h3 p).2.1⟩) hfd
  have e : (∏ᶠ p, LocNG.Datum.wt (d0 p) (d p)) = ∏ᶠ p, invVol (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) (MulAction.stabilizer ↥(FP p).UW0 (d p)) := finprod_congr fun p => ((h3 p).2.2).symm
  refine hm2.trans ?_
  rw [e]

end GlobalTheory.Unfold
end
end

section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.RatCls

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T T' : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {F' : LFlag (D.sp.Y 0) D.R.rS T'}

theorem principalPolarisation_exists_unique_section : (1 : GV D) ∈ H0 F F' := ⟨Subgroup.one_mem _, fun _ => rfl, fun _ => rfl⟩

theorem mul_mem_isometriesFixingBothFrames {g h : GV D} (hg : g ∈ H0 F F') (hh : h ∈ H0 F F') : g * h ∈ H0 F F' := by
  refine ⟨Subgroup.mul_mem _ hg.1 hh.1, fun a => ?_, fun a => ?_⟩
  · show g (h (frame F a)) = frame F a
    rw [hh.2.1 a, hg.2.1 a]
  · show g (h (frame F' a)) = frame F' a
    rw [hh.2.2 a, hg.2.2 a]

theorem inv_mem_isometriesFixingBothFrames {h : GV D} (hh : h ∈ H0 F F') : h⁻¹ ∈ H0 F F' := by
  refine ⟨Subgroup.inv_mem _ hh.1, fun a => ?_, fun a => ?_⟩
  · show h.symm (frame F a) = frame F a
    rw [LinearEquiv.symm_apply_eq, hh.2.1 a]
  · show h.symm (frame F' a) = frame F' a
    rw [LinearEquiv.symm_apply_eq, hh.2.2 a]

theorem ext_one (p : PlF D) : Ext p (1 : GV D) 1 := fun _ => rfl

theorem ext_mul {p : PlF D} {g h : GV D} {g' h' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p}
    (hg : Ext p g g') (hh : Ext p h h') : Ext p (g * h) (g' * h') := fun x => by
  show g' (h' (baseChange₂ D p x)) = baseChange₂ D p (g (h x))
  rw [hh x, hg (h x)]

theorem ext_inv {p : PlF D} {g : GV D} {g' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p}
    (hg : Ext p g g') : Ext p g⁻¹ g'⁻¹ := fun x => by
  show g'.symm (baseChange₂ D p x) = baseChange₂ D p (g.symm x)
  rw [LinearEquiv.symm_apply_eq, hg, LinearEquiv.apply_symm_apply]

end GlobalTheory.Unfold.RatCls


open GlobalTheory.Unfold.RatCls in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem GlobalTheory.Unfold.ratCls_agree : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → Equivalence (GRel (Z := Z) (FP := FP) F F') ∧ (∀ y y' : Dat Z FP, GRel F F' y y' → (stabY F F' y).encard = (stabY F F' y').encard) ∧ ∀ (Λ₁ Λ₂ : LV D) (y₁ y₂ : Dat Z FP), LocOver Λ₁ y₁ → LocOver Λ₂ y₂ → (LRel F F' Λ₁ Λ₂ ↔ GRel F F' y₁ y₂) ∧ stabL F F' Λ₁ = stabY F F' y₁ := by
  intro D X Y u u' F F' w hZ hG Z FP hB hR
  have hact : ∀ p, ∃ act : MulAction (FP p).UW0 (LocNG.Datum (FP p)),
      (∀ (g : (FP p).UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧
      ∀ d (g : (FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d := by
    intro p
    refine GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) ?_ (hR p)
    rw [finrank_Vp]
    obtain ⟨j, hj⟩ := D.R.m_even
    have h2 := D.R.two_le_m
    show D.R.k + D.R.m - 1 = D.R.k + 2 * (D.R.m / 2 - 1) + 1
    omega
  choose act hmv _ using hact
  obtain ⟨hu, hw, -, hlift⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hZ hG Z FP hB hR
  have hdict := GlobalTheory.T.globalInnerDatum_eq_iff_local_data_eq D X Y u u' F F' w hZ hG Z FP hB hR

  have rm_fun : ∀ h ∈ H0 F F', ∀ y y₁ y₂ : Dat Z FP, RMoves h y y₁ → RMoves h y y₂ → y₁ = y₂ := by
    intro h hh y y₁ y₂ r₁ r₂
    funext p
    obtain ⟨g₁, e₁, m₁⟩ := r₁ p
    obtain ⟨g₂, e₂, m₂⟩ := r₂ p
    obtain rfl : g₁ = g₂ := (hu h p).unique e₁ e₂
    have hm := hw h hh p g₁ e₁
    exact ((hmv p ⟨g₁, hm⟩ _ _).1 m₁).symm.trans ((hmv p ⟨g₁, hm⟩ _ _).1 m₂)
  have rm_one : ∀ y : Dat Z FP, RMoves (1 : GV D) y y := by
    intro y p
    refine ⟨1, ext_one p, (hmv p 1 _ _).2 ?_⟩
    letI := act p
    exact one_smul _ _
  have rm_mul : ∀ h₁ ∈ H0 F F', ∀ h₂ ∈ H0 F F', ∀ y y' y'' : Dat Z FP,
      RMoves h₁ y y' → RMoves h₂ y' y'' → RMoves (h₂ * h₁) y y'' := by
    intro h₁ hh₁ h₂ hh₂ y y' y'' r₁ r₂ p
    obtain ⟨g₁, e₁, m₁⟩ := r₁ p
    obtain ⟨g₂, e₂, m₂⟩ := r₂ p
    let a₁ : (FP p).UW0 := ⟨g₁, hw h₁ hh₁ p g₁ e₁⟩
    let a₂ : (FP p).UW0 := ⟨g₂, hw h₂ hh₂ p g₂ e₂⟩
    refine ⟨g₂ * g₁, ext_mul e₂ e₁, (hmv p (a₂ * a₁) _ _).2 ?_⟩
    letI := act p
    have f₁ : a₁ • y p = y' p := (hmv p a₁ _ _).1 m₁
    have f₂ : a₂ • y' p = y'' p := (hmv p a₂ _ _).1 m₂
    show (a₂ * a₁) • y p = y'' p
    rw [mul_smul, f₁, f₂]
  have rm_inv : ∀ h ∈ H0 F F', ∀ y y' : Dat Z FP, RMoves h y y' → RMoves h⁻¹ y' y := by
    intro h hh y y' r p
    obtain ⟨g, e, m⟩ := r p
    let a : (FP p).UW0 := ⟨g, hw h hh p g e⟩
    refine ⟨g⁻¹, ext_inv e, (hmv p a⁻¹ _ _).2 ?_⟩
    letI := act p
    have f : a • y p = y' p := (hmv p a _ _).1 m
    show a⁻¹ • y' p = y p
    rw [inv_smul_eq_iff, f]
  have conj : ∀ h ∈ H0 F F', ∀ y y' : Dat Z FP, RMoves h y y' →
      ∀ k ∈ stabY F F' y, h * k * h⁻¹ ∈ stabY F F' y' := by
    intro h hh y y' hm k hk
    refine ⟨mul_mem_isometriesFixingBothFrames (mul_mem_isometriesFixingBothFrames hh hk.1) (inv_mem_isometriesFixingBothFrames hh), ?_⟩
    rw [mul_assoc]
    exact rm_mul _ (mul_mem_isometriesFixingBothFrames hk.1 (inv_mem_isometriesFixingBothFrames hh)) h hh _ _ _
      (rm_mul _ (inv_mem_isometriesFixingBothFrames hh) k hk.1 _ _ _ (rm_inv h hh y y' hm) hk.2) hm
  refine ⟨⟨fun y => ⟨1, principalPolarisation_exists_unique_section, rm_one y⟩, fun ⟨h, hh, hm⟩ => ⟨h⁻¹, inv_mem_isometriesFixingBothFrames hh, rm_inv h hh _ _ hm⟩,
    fun ⟨h₁, hh₁, m₁⟩ ⟨h₂, hh₂, m₂⟩ => ⟨h₂ * h₁, mul_mem_isometriesFixingBothFrames hh₂ hh₁, rm_mul h₁ hh₁ h₂ hh₂ _ _ _ m₁ m₂⟩⟩, ?_, ?_⟩
  · rintro y y' ⟨h, hh, hm⟩
    have e : stabY F F' y' = (MulAut.conj h) '' stabY F F' y := by
      ext k
      constructor
      · intro hk
        refine ⟨h⁻¹ * k * h⁻¹⁻¹, conj h⁻¹ (inv_mem_isometriesFixingBothFrames hh) y' y (rm_inv h hh y y' hm) k hk, ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
      · rintro ⟨k, hk, rfl⟩
        exact conj h hh y y' hm k hk
    rw [e, (MulAut.conj h).injective.encard_image]
  · intro Λ₁ Λ₂ y₁ y₂ h₁ h₂
    have key : ∀ h ∈ H0 F F', ∀ (Λ Λ' : LV D) (y y' : Dat Z FP), LocOver Λ y → LocOver Λ' y' →
        (gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ) = gdat F F' Λ' ↔ RMoves h y y') := by
      intro h hh Λ Λ' y y' hl hl'
      obtain ⟨y'', hl'', hm''⟩ := hlift h hh Λ y hl
      rw [hdict _ _ y'' y' hl'' hl']
      constructor
      · rintro rfl
        exact hm''
      · intro hm
        exact rm_fun h hh y y'' y' hm'' hm
    refine ⟨⟨fun ⟨h, hh, he⟩ => ⟨h, hh, (key h hh _ _ _ _ h₁ h₂).1 he⟩,
      fun ⟨h, hh, hm⟩ => ⟨h, hh, (key h hh _ _ _ _ h₁ h₂).2 hm⟩⟩, ?_⟩
    ext h
    exact ⟨fun ⟨hh, he⟩ => ⟨hh, (key h hh _ _ _ _ h₁ h₁).1 he⟩, fun ⟨hh, hm⟩ => ⟨hh, (key h hh _ _ _ _ h₁ h₁).2 hm⟩⟩
end
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orbitCount_rows_doubleCosets_innerDatum_class : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D), TG F F' t₀ Λ₀ → ∀ K, K = {κ | ∃ (t : TauC Y u u') (Λ₁ : LV D), TG F F' t Λ₁ ∧ LRel F F' Λ₀ Λ₁ ∧ key t = κ} → K.Finite ∧ (∀ κ ∈ K, ∃ t : TauC Y u u', TG F F' t Λ₀ ∧ key t = κ) ∧ (∀ (t : TauC Y u u') (Λ₁ : LV D), TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → wt t = wt t₀) ∧ (K.encard : ℝ≥0∞) * ENNReal.ofReal (wt t₀ ^ 2) = (((stabL F F' Λ₀).encard : ℝ≥0∞))⁻¹ := by
  first | exact @GlobalTheory.OrbitCount.orbit_count | exact GlobalTheory.OrbitCount.orbit_count | (intros; apply GlobalTheory.OrbitCount.orbit_count <;> assumption)
end

section


theorem _root_.GlobalTheory.T.termPairs_rowLattice_counted_via_embeddings : GlobalTheory.TypeAsm.PerRowC := by
  first | exact @GlobalTheory.TypeAsm.perRowC | exact GlobalTheory.TypeAsm.perRowC | (intros; apply GlobalTheory.TypeAsm.perRowC <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rowTerm_of_local_completions_terms : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∃ t : TauC Y u u', TG F F' t Λ := by
  first | exact @GlobalTheory.RowTermReal.exists_term_of_locOver | exact GlobalTheory.RowTermReal.exists_term_of_locOver | (intros; apply GlobalTheory.RowTermReal.exists_term_of_locOver <;> assumption)
end
