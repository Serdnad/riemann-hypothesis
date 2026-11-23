module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle140
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle322
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle161
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle146
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle049
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Cases
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas.VolRatio

section Congr

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]

theorem fDeg_congr (e : K ≃+* L) : Formalism.HermitianLatticesTheory.fDeg K = Formalism.HermitianLatticesTheory.fDeg L := by
  unfold Formalism.HermitianLatticesTheory.fDeg
  refine Fintype.card_congr
    { toFun := fun w => w.comap (e.symm : L →+* K)
      invFun := fun w => w.comap (e : K →+* L)
      left_inv := fun w => ?_
      right_inv := fun w => ?_ }
  · ext x
    simp
  · ext x
    simp

theorem vInv_congr (e : K ≃+* L) : Formalism.HermitianLatticesTheory.vInv K = Formalism.HermitianLatticesTheory.vInv L := by
  unfold Formalism.HermitianLatticesTheory.vInv
  rw [fDeg_congr e, NumberField.discr_eq_discr_of_ringEquiv K e]

variable [StarRing K] [StarRing L]

theorem conjIdeal_comap (e : K ≃+* L) (he : ∀ x, e (star x) = star (e x)) (P : Ideal (𝓞 L)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) (P.comap (RingOfIntegers.mapRingEquiv e)) =
      (Formalism.HermitianLatticesTheory.conjIdeal (K := L) P).comap (RingOfIntegers.mapRingEquiv e) := by
  set g := RingOfIntegers.mapRingEquiv e with hg
  have hge : ∀ x : 𝓞 K, algebraMap (𝓞 L) L (g x) = e (algebraMap (𝓞 K) K x) := fun x => rfl
  unfold Formalism.HermitianLatticesTheory.conjIdeal
  conv_rhs => rw [← Ideal.map_symm, Ideal.map_span]
  congr 1
  ext r
  constructor
  · rintro ⟨s, hs, hr⟩
    exact ⟨g r, ⟨g s, hs, by rw [hge, hge, hr, he]⟩, g.symm_apply_apply r⟩
  · rintro ⟨t, ⟨s, hs, ht⟩, rfl⟩
    refine ⟨g.symm s, by simpa only [Ideal.mem_comap, RingEquiv.apply_symm_apply] using hs, e.injective ?_⟩
    rw [he, ← hge, ← hge, g.apply_symm_apply, g.apply_symm_apply, ht]

theorem eulerFac_comap (e : K ≃+* L) (he : ∀ x, e (star x) = star (e x)) (M : ℕ) (P : Ideal (𝓞 L)) :
    Formalism.HermitianLatticesTheory.eulerFac K M (P.comap (RingOfIntegers.mapRingEquiv e)) = Formalism.HermitianLatticesTheory.eulerFac L M P := by
  have hN : Ideal.absNorm (P.comap (RingOfIntegers.mapRingEquiv e)) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv _ P (RingOfIntegers.mapRingEquiv e)
      (Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv e).surjective P).symm).toEquiv
  have hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (P.comap (RingOfIntegers.mapRingEquiv e)) =
      P.comap (RingOfIntegers.mapRingEquiv e) ↔ Formalism.HermitianLatticesTheory.conjIdeal (K := L) P = P := by
    rw [conjIdeal_comap e he]
    exact (Ideal.comap_injective_of_surjective _ (RingOfIntegers.mapRingEquiv e).surjective).eq_iff
  unfold Formalism.HermitianLatticesTheory.eulerFac
  rw [hN]
  by_cases h : Formalism.HermitianLatticesTheory.conjIdeal (K := L) P = P
  · rw [if_pos h, if_pos (hc.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hc.1 h'))]

theorem lValEta_congr (e : K ≃+* L) (he : ∀ x, e (star x) = star (e x)) (M : ℕ) :
    Formalism.HermitianLatticesTheory.lValEta K M = Formalism.HermitianLatticesTheory.lValEta L M := by
  unfold Formalism.HermitianLatticesTheory.lValEta
  let g := RingOfIntegers.mapRingEquiv e
  let φ : {P : Ideal (𝓞 L) // P.IsMaximal} ≃ {P : Ideal (𝓞 K) // P.IsMaximal} :=
    { toFun := fun P => ⟨P.1.comap g, by
        haveI := P.2
        exact Ideal.comap_isMaximal_of_surjective g g.surjective⟩
      invFun := fun P => ⟨P.1.comap g.symm, by
        haveI := P.2
        exact Ideal.comap_isMaximal_of_surjective g.symm g.symm.surjective⟩
      left_inv := fun P => by
        ext x
        simp only [Ideal.mem_comap, RingEquiv.apply_symm_apply]
      right_inv := fun P => by
        ext x
        simp only [Ideal.mem_comap, RingEquiv.symm_apply_apply] }
  rw [← φ.tprod_eq]
  exact tprod_congr fun P => eulerFac_comap e he M P.1

theorem rankFac_congr (e : K ≃+* L) (he : ∀ x, e (star x) = star (e x)) (M : ℕ) :
    rankFac K M = rankFac L M := by
  unfold rankFac
  rw [fDeg_congr e, vInv_congr e, lValEta_congr e he]

theorem eulerFac_nonneg (M : ℕ) (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    0 ≤ Formalism.HermitianLatticesTheory.eulerFac K M P := by
  have h0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm P : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h0
  unfold Formalism.HermitianLatticesTheory.eulerFac
  split_ifs
  · have h2 : (1 : ℝ) ≤ Real.sqrt (Ideal.absNorm P : ℝ) := Real.one_le_sqrt.2 h1
    have h3 : Real.sqrt (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ h2 (by omega)
    have h4 : 0 ≤ Real.sqrt (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) := by positivity
    refine inv_nonneg.2 ?_
    rcases neg_one_pow_eq_or ℝ M with h | h <;> rw [h] <;> linarith
  · have h3 : (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ h1 (by omega)
    exact Real.rpow_nonneg (by linarith) _

theorem rankFac_nonneg (M : ℕ) : 0 ≤ rankFac K M := by
  have h : 0 ≤ Formalism.HermitianLatticesTheory.lValEta K M := tprod_nonneg fun P => eulerFac_nonneg M P.1 P.2
  have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv K := by
    unfold Formalism.HermitianLatticesTheory.vInv
    positivity
  unfold rankFac
  positivity

end Congr

theorem volU_pos (i : ℕ) : 0 < volU i := by
  have : 0 < sphV i := by
    unfold sphV
    exact Finset.prod_pos fun l _ => by have := Real.pi_pos; positivity
  unfold volU
  positivity

theorem ennreal_volume_ratio_step_cancel (X Y : ENNReal) (r a b ρ : ℝ) (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b)
    (hρ : ρ * a = r * b)
    (h : X / ENNReal.ofReal a = Y / ENNReal.ofReal b * ENNReal.ofReal ρ) :
    X = Y * ENNReal.ofReal r := by
  have e2 : ρ = b * (r / a) := by field_simp; linarith
  rw [e2, ENNReal.ofReal_mul hb.le, ← mul_assoc,
    ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 hb).ne' ENNReal.ofReal_ne_top,
    ENNReal.ofReal_div_of_pos ha, ← mul_div_assoc] at h
  have h0 := (ENNReal.ofReal_pos.2 ha).ne'
  rw [← ENNReal.div_mul_cancel (a := ENNReal.ofReal a) (b := X) h0 ENNReal.ofReal_ne_top, h,
    ENNReal.div_mul_cancel h0 ENNReal.ofReal_ne_top]

theorem sameField_trans {I I' I'' : AutInst} (h : SameField I I') (h' : SameField I' I'') :
    SameField I I'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e'.trans e, fun x => by simp [he, he']⟩

theorem sameField_symm {I I' : AutInst} (h : SameField I I') : SameField I' I := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun x => e.injective ?_⟩
  simp [he]

theorem step (hstep : VolumeStep) (I : AutInst) (P Q : ℕ) (h : HasSig I P Q) (h3 : 3 ≤ P + Q) (s : Bool)
    (hs : if s then 1 ≤ P else 1 ≤ Q) :
    ∃ I' : AutInst, SameField I I' ∧ HasSig I' (if s then P - 1 else P) (if s then Q else Q - 1) ∧
      ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
        (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure],
        IsGaugeAll I c → IsGaugeAll I' c' →
        gaugeVol I c μf = gaugeVol I' c' μf' * ENNReal.ofReal (rankFac I.E (P + Q)) := by
  obtain ⟨hf, -, -, -, -, hpq⟩ := GlobalTheory.T.autInst_degree_rootDiscriminant_rank I
  have hn := hpq P Q h
  obtain ⟨I', e, x, A, he, hn', -, -, -, hsig, hv⟩ := hstep I P Q h (by omega) s hs
  refine ⟨I', ⟨e, he⟩, hsig, ?_⟩
  intro c μf _ _ c' μf' _ _ hc hc'
  have hR := GlobalTheory.T.mass_ratio_rank_factor I.E I.n (by omega)
  rw [hf, show I.n - 1 = I'.n by omega] at hR
  rw [hn]
  exact ennreal_volume_ratio_step_cancel _ _ _ _ _ _ (rankFac_nonneg _) (pow_pos (volU_pos _) _) (pow_pos (volU_pos _) _) hR
    (hv c μf c' μf' hc hc')

theorem volumeRatio_of_volumeStep : VolumeStep → VolumeRatio := by
  intro hstep I p q p₀ q₀ hsig hp hq h2
  induction' hd : (p - p₀) + (q - q₀) with d ih generalizing I p q
  · obtain rfl : p₀ = p := by omega
    obtain rfl : q₀ = q := by omega
    refine ⟨⟨I, ⟨RingEquiv.refl _, fun _ => rfl⟩, hsig⟩, ?_⟩
    intro I₀ hI hsig₀ c μf _ _ c₀ μ₀ _ _ hc hc₀
    rw [Finset.Ioc_self, Finset.prod_empty, ENNReal.ofReal_one, mul_one]
    exact GlobalTheory.T.hermitian_volume_depends_only_on_field_signature I I₀ _ _ hI hsig hsig₀ c μf c₀ μ₀ hc hc₀
  · obtain ⟨I', p', q', hI', hsig', hp', hq', hsum, hv⟩ : ∃ (I' : AutInst) (p' q' : ℕ), SameField I I' ∧
        HasSig I' p' q' ∧ p₀ ≤ p' ∧ q₀ ≤ q' ∧ p' + q' + 1 = p + q ∧
        ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
          (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure],
          IsGaugeAll I c → IsGaugeAll I' c' →
          gaugeVol I c μf = gaugeVol I' c' μf' * ENNReal.ofReal (rankFac I.E (p + q)) := by
      by_cases hpp : p₀ < p
      · obtain ⟨I', h1, h2, h3⟩ := step hstep I p q hsig (by omega) true (by simp; omega)
        exact ⟨I', p - 1, q, h1, h2, by omega, hq, by omega, h3⟩
      · obtain ⟨I', h1, h2, h3⟩ := step hstep I p q hsig (by omega) false (by simp; omega)
        exact ⟨I', p, q - 1, h1, h2, hp, by omega, by omega, h3⟩
    obtain ⟨⟨I₁, hI₁, hsig₁⟩, hrat⟩ := ih I' p' q' hsig' hp' hq' (by omega)
    refine ⟨⟨I₁, sameField_trans hI' hI₁, hsig₁⟩, ?_⟩
    intro I₀ hI hsig₀ c μf _ _ c₀ μ₀ _ _ hc hc₀
    obtain ⟨μ', hH, hS⟩ := GlobalTheory.CongTop.exists_haar_sigmaFinite I'
    choose c' _ hc' _ using fun v : InfinitePlace I'.F => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I'.n (I'.ε v)
    have hg' : IsGaugeAll I' c' := hc'
    rw [hv c μf c' μ' hc hg', hrat I₀ (sameField_trans (sameField_symm hI') hI) hsig₀ c' μ' c₀ μ₀ hg' hc₀,
      ← hsum, Finset.prod_Ioc_succ_top (by omega),
      ENNReal.ofReal_mul (Finset.prod_nonneg fun M _ => rankFac_nonneg M), mul_assoc]
    obtain ⟨e, he⟩ := hI'
    simp only [rankFac_congr e he]

end GlobalTheory.FlagMeas.VolRatio
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.HL
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BBTie

namespace GlobalTheory.DiffLoc

theorem ddS_ne (D : D7) : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · exact FaithfulSMul.algebraMap_injective _ _

theorem mem_ddPow_neg_iff : ∀ (D : D7) (Z : LocDat D) (n : ℕ), n ≤ D.R.rS → ∀ y : D.host.E,
    y ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔
      ∀ p : PlF D, (D.s.atP p).ιE y * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ n ∈ (Z.M p).L.O := by
  intro D Z n hn y
  let a : Fin (D.R.rS + 1) := ⟨D.R.rS - n, by omega⟩
  have he : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = n := by
    show ((D.R.rS : ℤ) - ((D.R.rS - n : ℕ) : ℤ)) = n
    rw [Nat.cast_sub hn]; ring
  have hspan : ∀ p : PlF D, Submodule.span (Z.M p).L.O ((D.s.atP p).ιE ''
      ((ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)) =
      Submodule.span (Z.M p).L.O {frFac Z.δ p a} := by
    intro p
    have h := locDiffC_holds D Z p a
    rw [he] at h
    exact h
  have hf : ∀ p : PlF D, frFac Z.δ p a * btT Z p ^ n = 1 := by
    intro p
    rw [bt_frFac_eq Z p a]
    have hk : D.R.rS - a.val = n := by show D.R.rS - (D.R.rS - n) = n; omega
    rw [hk]
    set U := (bt_T_unit Z p).unit
    have hU : (U : (D.s.atP p).Ep) = btT Z p := IsUnit.unit_spec _
    rw [← hU, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
  have hinv : ∀ z : D.host.E, z ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔
      ∀ d ∈ ddS D ^ n, z * d ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro z
    rw [zpow_neg, zpow_natCast, FractionalIdeal.mem_inv_iff (pow_ne_zero n (ddS_ne D))]
  constructor
  · intro hy p
    have hm : (D.s.atP p).ιE y ∈ Submodule.span (Z.M p).L.O {frFac Z.δ p a} := by
      rw [← hspan p]; exact Submodule.subset_span ⟨y, hy, rfl⟩
    obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hm
    change (D.s.atP p).ιE y * btT Z p ^ n ∈ (Z.M p).L.O
    rw [← ho, Subring.smul_def, smul_eq_mul, mul_assoc, hf p, mul_one]
    exact o.2
  · intro h
    rw [hinv]
    intro d hd
    rw [FractionalIdeal.mem_one_iff]
    have hloc : ∀ p : PlF D, (D.s.atP p).ιE (y * d) ∈ (Z.M p).L.O := by
      intro p
      have hmem : ∀ x ∈ Submodule.span (Z.M p).L.O ((D.s.atP p).ιE ''
          ((ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)),
          (D.s.atP p).ιE d * x ∈ (Z.M p).L.O := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨z, hz, rfl⟩ := hx
          obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 ((hinv z).1 hz d hd)
          rw [← map_mul, mul_comm, ← ho]
          exact bt_iota_int Z p o
        | zero => rw [mul_zero]; exact Subring.zero_mem _
        | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
        | smul o x _ hx => rw [Subring.smul_def, smul_eq_mul, mul_left_comm]; exact mul_mem o.2 hx
      have hdf : (D.s.atP p).ιE d * frFac Z.δ p a ∈ (Z.M p).L.O :=
        hmem _ (by rw [hspan p]; exact Submodule.subset_span (Set.mem_singleton _))
      have hyp : (D.s.atP p).ιE y * btT Z p ^ n ∈ (Z.M p).L.O := h p
      have e : (D.s.atP p).ιE (y * d) =
          ((D.s.atP p).ιE y * btT Z p ^ n) * ((D.s.atP p).ιE d * frFac Z.δ p a) := by
        calc (D.s.atP p).ιE (y * d) = (D.s.atP p).ιE y * (D.s.atP p).ιE d * (frFac Z.δ p a * btT Z p ^ n) := by
              rw [hf p, mul_one, map_mul]
          _ = _ := by ring
      rw [e]
      exact mul_mem hyp hdf
    obtain ⟨o, ho⟩ := ((GlobalTheory.HL.PlacesInt.integers_local (placesOf Z)).1 (y * d)).1 hloc
    exact ⟨o, ho⟩

end GlobalTheory.DiffLoc
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped nonZeroDivisors

namespace GlobalTheory.FrameFactorUnit

open Formalism.MainNotions.S.LocNG IsDedekindDomain
open scoped nonZeroDivisors

variable {D : D7}

theorem ddS_ne_zero : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · exact FaithfulSMul.algebraMap_injective _ _

theorem one_mem_inv_pow (k : ℕ) : (1 : D.host.E) ∈ (ddS D)⁻¹ ^ k := by
  have hle : ddS D ≤ 1 := by
    unfold ddS
    exact FractionalIdeal.coeIdeal_le_one
  have h1 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ (ddS D)⁻¹ := by
    simpa using FractionalIdeal.inv_anti_mono ddS_ne_zero hle
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    simpa using FractionalIdeal.mul_mem_mul ih (h1 (FractionalIdeal.one_mem_one _))

private theorem exists_nat_mul_mem_ringOfIntegers_of_fractionalIdeal {E : Type} [Field E] [NumberField E]
    (J : FractionalIdeal (𝓞 E)⁰ E) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ y ∈ J, ∃ z : 𝓞 E, (N : E) * y = (z : E) := by
  obtain ⟨b, hb, hint⟩ := J.isFractional
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hb0
  · intro y hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))
    obtain ⟨z, hz⟩ := hint y hy
    refine ⟨c * z, ?_⟩
    have hz' : (z : E) = (b : E) * y := by
      rw [Algebra.smul_def] at hz
      exact hz
    have hN : ((Ideal.absNorm (Ideal.span {b}) : 𝓞 E) : E) = (Ideal.absNorm (Ideal.span {b}) : E) := by
      push_cast
      rfl
    calc (Ideal.absNorm (Ideal.span {b}) : E) * y
        = ((c * b : 𝓞 E) : E) * y := by rw [hc, hN]
      _ = (c : E) * ((b : E) * y) := by push_cast; ring
      _ = (c : E) * (z : E) := by rw [hz']
      _ = ((c * z : 𝓞 E) : E) := by push_cast; ring

private theorem ιE_ringOfIntegers_mem_O (D : D7) (p : PlF D) (z : 𝓞 D.host.E) :
    (D.s.atP p).ιE (z : D.host.E) ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  have h : IsIntegral ℤ ((D.s.atP p).ιE (z : D.host.E)) :=
    (RingOfIntegers.isIntegral_coe z).map ((D.s.atP p).ιE.toIntAlgHom)
  exact h.tower_top

private theorem finite_setOf_not_isUnit_natCast_atP (D : D7) (N : ℕ) (hN : N ≠ 0) :
    {p : PlF D | ¬ ∃ w ∈ (D.s.atP p).O, (D.s.atP p).ιE (N : D.host.E) * w = 1}.Finite := by
  have hI : Ideal.span {(N : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hmem
  apply hp
  have hv : p.valuation D.host.F (N : D.host.F) = 1 := by
    have := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
      (K := D.host.F) (v := p)).mpr hmem
    simpa using this
  have hle : (D.s.atP p).ιF ((N : D.host.F)⁻¹) ≤ᵥ (D.s.atP p).ιF 1 := by
    rw [(D.s.atP p).val]
    simp [map_inv₀, hv]
  rw [map_one] at hle
  have hint : (D.s.atP p).ιF ((N : D.host.F)⁻¹) ∈ Valuation.integer (ValuativeRel.valuation (D.s.atP p).Fp) := by
    rw [Valuation.mem_integer_iff, ← (ValuativeRel.valuation _).vle_one_iff]
    exact hle
  have hNE : (N : D.host.E) ≠ 0 := by exact_mod_cast hN
  refine ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((N : D.host.F)⁻¹)), ?_, ?_⟩
  · rw [(D.s.atP p).O_def]
    exact isIntegral_algebraMap (R := Valuation.integer (ValuativeRel.valuation (D.s.atP p).Fp)) (A := (D.s.atP p).Ep) (x := ⟨_, hint⟩)
  · rw [← (D.s.atP p).compat, ← map_mul, map_inv₀, map_natCast, mul_inv_cancel₀ hNE, map_one]

end GlobalTheory.FrameFactorUnit


open GlobalTheory.FrameFactorUnit in
theorem GlobalTheory.FrameFactorUnit.frFac_isUnitO_finite : ∀ (D : D7) (Z : LocDat D) (a : Fin (D.R.rS + 1)),
    {p : PlF D | ¬ Formalism.MainNotions.S.LocNG.IsUnitO (Z.M p) (frFac Z.δ p a)}.Finite := by
  intro D Z a
  have hL := Formalism.L2.SG.Pf.locDiffC_holds D Z
  unfold Formalism.L2.SG.Pf.LocDiffC at hL
  obtain ⟨N, hN0, hN⟩ := exists_nat_mul_mem_ringOfIntegers_of_fractionalIdeal (ddS D ^ (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))))
  refine (finite_setOf_not_isUnit_natCast_atP D N hN0).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  intro hgood
  apply hp
  obtain ⟨w, hwO, hw1⟩ := hgood
  have hO := Formalism.L2.SG.Pf.LocFacts.lf_hO Z p
  have hc : Formalism.L2.SG.Pf.LocFacts.cP p Z ^ (D.R.rS - a.val) ∈ (D.s.atP p).O := by
    have := Formalism.L2.SG.Pf.LocFacts.lf_mem_pow p Formalism.L2.SG.Pf.dualLoc_holds Z (D.R.rS - a.val) 1
      (one_mem_inv_pow _)
    simpa using this
  have hunit : IsUnit (Formalism.L2.SG.Pf.LocFacts.cP p Z ^ (D.R.rS - a.val)) :=
    (Formalism.L2.SG.Pf.LocFacts.isUnit_localConstant p Z).pow _
  have hinv : frFac Z.δ p a * Formalism.L2.SG.Pf.LocFacts.cP p Z ^ (D.R.rS - a.val) = 1 := by
    unfold frFac
    exact Ring.inverse_mul_cancel _ hunit
  have hmem : frFac Z.δ p a ∈ (Z.M p).L.O := by
    have hs := Submodule.mem_span_singleton_self (R := (Z.M p).L.O) (frFac Z.δ p a)
    rw [← hL p a] at hs
    revert hs
    generalize frFac Z.δ p a = f
    intro hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, hz⟩ := hN y hy
      rw [hO]
      have hy' : (D.s.atP p).ιE y = w * (D.s.atP p).ιE (z : D.host.E) := by
        rw [← hz, map_mul, ← mul_assoc, mul_comm w, hw1, one_mul]
      rw [hy']
      exact mul_mem hwO (ιE_ringOfIntegers_mem_O D p z)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul r x _ hx =>
      rw [Subring.smul_def]
      exact mul_mem r.2 hx
  show frFac Z.δ p a ∈ (Z.M p).L.O ∧ ∃ y ∈ (Z.M p).L.O, frFac Z.δ p a * y = 1
  exact ⟨hmem, _, hO ▸ hc, hinv⟩
end
