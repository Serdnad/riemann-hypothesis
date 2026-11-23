module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Bundle001
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal

@[expose] public section

section

noncomputable section

namespace PI.CntNotIntW

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocGen : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (p : PlF D) (m : ℕ), ∃ x : D.host.E,
      x ∈ ((ddS D) ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ∧ star x = x ∧
      ∃ w ∈ (D.s.atP p).O,
        Ring.inverse ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ m) =
          w * (D.s.atP p).ιE x

theorem ringInverse_mulEquiv {R S : Type*} [MonoidWithZero R] [MonoidWithZero S] (f : R ≃* S) (x : R) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  have f0 : f 0 = 0 := by
    calc f 0 = f (0 * f.symm 0) := by rw [zero_mul]
      _ = f 0 * f (f.symm 0) := map_mul f _ _
      _ = 0 := by rw [f.apply_symm_apply, mul_zero]
  by_cases h : IsUnit x
  · obtain ⟨u, rfl⟩ := h
    have e : f u = ((Units.map f.toMonoidHom u : Sˣ) : S) := rfl
    rw [Ring.inverse_unit, e, Ring.inverse_unit]
    rfl
  · have hf : ¬ IsUnit (f x) := fun hu => h (by simpa using hu.map f.symm)
    rw [Ring.inverse_non_unit x h, Ring.inverse_non_unit _ hf]
    exact f0

theorem iE_mem_O (D : Formalism.BasicNotions.D7) (p : PlF D) (o : 𝓞 D.host.E) : (D.s.atP p).ιE (o : D.host.E) ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  have h1 : IsIntegral ℤ ((D.s.atP p).ιE (o : D.host.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe o).map (D.s.atP p).ιE.toIntAlgHom
  exact h1.tower_top

theorem cj_frFac (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (a : Fin (D.R.rS + 1)) :
    (D.s.atP p).cj (frFac δ p a) = frFac δ p a := by
  unfold frFac
  rw [show ∀ x, (D.s.atP p).cj (Ring.inverse x) = Ring.inverse ((D.s.atP p).cj x) from
    fun x => ringInverse_mulEquiv (D.s.atP p).cj.toMulEquiv x]
  rw [map_pow, map_mul, AlgEquiv.commutes, (D.s.atP p).cj_ιE, map_ratCast]

theorem frame_mem {D : Formalism.BasicNotions.D7} {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (F : LFlag (D.sp.Y 0) D.R.rS T) (hX : XLam Λ F = XS D F.fl) (hz : F.fl.z ∈ Λ) (a : Fin (D.R.rS + 1))
    (x : D.host.E)
    (hx : x ∈ ((ddS D) ^ (-((D.R.rS - a.val : ℕ) : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) :
    x • F.fl.fvec a ∈ Λ := by
  have hXS : XS D F.fl ≤ Λ := by
    rw [← hX]
    unfold XLam
    exact inf_le_left
  induction a using Fin.lastCases with
  | last =>
    unfold FlagG.fvec
    rw [Fin.snoc_last]
    simp only [Fin.val_last, Nat.sub_self, Nat.cast_zero, neg_zero, zpow_zero] at hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
    rw [algebraMap_smul]
    exact Λ.smul_mem o hz
  | cast b =>
    have e1 : (-((D.R.rS - (Fin.castSucc b).val : ℕ) : ℤ)) = -((D.R.rS : ℤ) - ((b : ℕ) : ℤ)) := by
      rw [Fin.coe_castSucc, Nat.cast_sub b.isLt.le]
    rw [e1] at hx
    have hmem : x • F.fl.e b ∈ XS D F.fl := by
      unfold XS
      apply Submodule.subset_span
      exact ⟨b, x, hx, rfl⟩
    unfold FlagG.fvec
    rw [Fin.snoc_castSucc]
    exact hXS hmem

end PI.CntNotIntW
end
end

section

noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TrDual : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (p : PlF D), ∀ c ∈ 𝒪[(D.s.atP p).Fp],
      haveI : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
      ‖Algebra.trace ℚ_[Loc.resChar p] (D.s.atP p).Fp (c * (δ p)⁻¹)‖ ≤ 1

def DualApprox : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) [Fact (Loc.resChar p).Prime]
    (Fp : Type) [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp]
    [Algebra ℚ_[Loc.resChar p] Fp], Continuous (algebraMap ℚ_[Loc.resChar p] Fp) →
    FiniteDimensional ℚ_[Loc.resChar p] Fp → ∀ (ι : K →+* Fp), DenseRange ι →
    (∀ x y : K, (ι x ≤ᵥ ι y) ↔ p.valuation K x ≤ p.valuation K y) →
    ∀ z : Fp, (∀ c ∈ 𝒪[Fp], ‖Algebra.trace ℚ_[Loc.resChar p] Fp (c * z)‖ ≤ 1) →
    ∀ k : ℕ, ∃ t : K, (∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (t * a) = n) ∧
      ∃ μ ∈ 𝒪[Fp], ι t = z + ((Loc.resChar p : ℕ) : Fp) ^ k * μ

def LocDiff : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (p : PlF D), ∃ t : D.host.F,
      (∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (t * a) = n) ∧
      δ p * (D.s.atP p).ιF t ≠ 0 ∧ δ p * (D.s.atP p).ιF t ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p * (D.s.atP p).ιF t)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]

def PowSmall : Prop :=
  ∀ (Fp : Type) [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp] (x y : Fp),
    valuation Fp y < 1 → ∃ k : ℕ, valuation Fp (y ^ k * x) < 1

def DualPow : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (t : D.host.F), (∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (t * a) = n) →
    ∀ m : ℕ, ((t : D.host.E) ^ m) ∈
      ((ddS D) ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

end PI.CntNotIntW
end
end

section

noncomputable section

namespace PI.CntNotIntW

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def NormAt {L : Loc.LocE F E} (g : Loc.SplitG L) {r : ℕ} (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) : Prop :=
  (∃ s : 𝒪[F], (g.e (Zh a b)).1 + (if a = Fin.last r ∧ b = Fin.last r then T else 0) = (g.q : F) * s) ∧
  (∃ s : 𝒪[F], (g.e (Zh a b)).2 + (if a = Fin.last r ∧ b = Fin.last r then T else 0) = (g.q : F) * s) ∧
  (∃ s : 𝒪[F], (g.e (Zh a b)).1 + (g.e (Zh b a)).2 + (if a = Fin.last r ∧ b = Fin.last r then T + T' else 0) =
    (g.q : F) ^ 2 * s)

theorem mem_R_split (M : Loc.Model F E) (g : Loc.SplitG M.L) (hs : M.split = some g) (x : E) (s1 s2 : 𝒪[F])
    (he : g.e x = ((s1 : F), (s2 : F))) (hc : s1 - s2 ∈ Ideal.span {g.q}) : x ∈ M.R := by
  unfold Loc.Model.R
  rw [hs]
  simp only [Subring.mem_comap, Subring.mem_map]
  refine ⟨(s1, s2), ?_, ?_⟩
  · rw [RingHom.mem_eqLocus]
    simp only [RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_snd]
    exact Ideal.Quotient.eq.2 hc
  · simp [he]

theorem zzplus_mem (M : Loc.Model F E) (g : Loc.SplitG M.L) (hs : M.split = some g) {r : ℕ}
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (hTT : ∃ k : 𝒪[F], T - T' = (g.q : F) * k)
    (h : ∀ a b, NormAt g Zh T T' a b) (a b : Fin (r + 1)) : Loc.HermSp.ZZplusOf M Zh T T' a b ∈ M.R := by
  have hq : (g.q : F) ≠ 0 := by
    intro h0
    have : g.q = 0 := Subtype.ext h0
    exact g.q_irr.ne_zero this
  obtain ⟨k, hk⟩ := hTT
  obtain ⟨⟨s1, hs1⟩, -, ⟨s3, hs3⟩⟩ := h a b
  obtain ⟨-, ⟨s2, hs2⟩, -⟩ := h b a
  set c : Prop := a = Fin.last r ∧ b = Fin.last r with hc_def
  have hcs : (b = Fin.last r ∧ a = Fin.last r) ↔ c := and_comm
  unfold Loc.HermSp.ZZplusOf
  rw [hs]
  simp only [Matrix.of_apply]
  by_cases hcc : c
  · have hcc' : b = Fin.last r ∧ a = Fin.last r := hcs.2 hcc
    rw [if_pos hcc]
    rw [if_pos hcc] at hs1 hs3
    rw [if_pos hcc'] at hs2
    refine mem_R_split M g hs _ s1 (k - s2) ?_ ?_
    · rw [map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      ext
      · simp only [Prod.fst_sub]
        field_simp
        linear_combination hs1
      · simp only [Prod.snd_sub]
        push_cast
        field_simp
        linear_combination -hs2 + hk
    · rw [Ideal.mem_span_singleton']
      refine ⟨s3, ?_⟩
      apply Subtype.ext
      push_cast
      apply mul_left_cancel₀ hq
      linear_combination hs1 + hs2 - hs3 - hk
  · rw [if_neg hcc, sub_zero]
    have hcc' : ¬ (b = Fin.last r ∧ a = Fin.last r) := fun h' => hcc (hcs.1 h')
    rw [if_neg hcc, add_zero] at hs1
    rw [if_neg hcc, add_zero] at hs3
    rw [if_neg hcc', add_zero] at hs2
    refine mem_R_split M g hs _ s1 (-s2) ?_ ?_
    · rw [AlgEquiv.apply_symm_apply]
      ext
      · simp only
        field_simp
        linear_combination hs1
      · simp only
        push_cast
        field_simp
        linear_combination -hs2
    · rw [Ideal.mem_span_singleton']
      refine ⟨s3, ?_⟩
      apply Subtype.ext
      push_cast
      apply mul_left_cancel₀ hq
      linear_combination hs1 + hs2 - hs3

end Generic

theorem tt_mod_q (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word)
    (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (p : PlF D) (g : Loc.SplitG (M p).L)
    (hs : (M p).split = some g) :
    ∃ k : 𝒪[(D.s.atP p).Fp], (((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) - (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) =
      (g.q : (D.s.atP p).Fp) * k := by
  have hm := (hA p).2.2.2.2.2
  rw [hs] at hm
  rcases hsp : (D.s.atP p).split with _ | sg
  · rw [hsp] at hm
    exact hm.elim
  · rw [hsp] at hm
    have hqq : g.q = sg.q := hm.2
    have hell : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := (D.s_split p).1 (by rw [hsp]; rfl)
    have hdvd : Loc.resChar p ∣ Lat.gS D ^ 2 := by
      apply Dvd.dvd.pow _ two_ne_zero
      unfold Lat.gS
      rcases Finset.mem_insert.1 hell with h0 | h1
      · rw [h0]; exact dvd_mul_right _ _
      · rw [Finset.mem_singleton.1 h1]; exact dvd_mul_left _ _
    have hmod : (D.mem u).A.T ≡ (D.mem u').A.T [MOD Loc.resChar p] := Nat.ModEq.of_dvd hdvd hT
    have hz : ((Loc.resChar p : ℕ) : ℤ) ∣ ((D.mem u').A.T : ℤ) - ((D.mem u).A.T : ℤ) :=
      (Nat.modEq_iff_dvd).1 hmod
    obtain ⟨k, hk⟩ := hz
    refine ⟨⟨((-k : ℤ) : (D.s.atP p).Fp), intCast_mem _ (-k)⟩, ?_⟩
    rw [hqq, sg.q_eq]
    have hk' : (((D.mem u').A.T : ℤ) : (D.s.atP p).Fp) - (((D.mem u).A.T : ℤ) : (D.s.atP p).Fp) =
        (((Loc.resChar p : ℕ) : ℤ) : (D.s.atP p).Fp) * ((k : ℤ) : (D.s.atP p).Fp) := by
      rw [← Int.cast_sub, hk, Int.cast_mul]
    simp only [Int.cast_natCast] at hk'
    push_cast
    linear_combination -hk'

end PI.CntNotIntW
end
end

section

noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem flag_gram {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}
    (F : FlagG S r T) (a b : Fin (r + 1)) :
    S.hT (F.fvec a) (F.fvec b) = if a = Fin.last r ∧ b = Fin.last r then -T else 0 := by
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, F.z_norm]
    | cast j =>
      have h := S.herm.eq (F.e j) F.z
      rw [F.z_orth, map_zero] at h
      simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc]
      rw [← h]
      simp [Fin.castSucc_ne_last]
  | cast i =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, F.z_orth, Fin.castSucc_ne_last]
    | cast j => simp [FlagG.fvec, F.e_iso, Fin.castSucc_ne_last]

theorem frameAct_one {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {n : ℕ}
    (f : Fin n → S.V) : frameAct f (1 : Matrix (Fin n) (Fin n) (𝓞 E)) = f := by
  funext b
  unfold frameAct
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [Matrix.one_apply_ne hc]
  · simp

theorem star_eq_conjF (D : Formalism.BasicNotions.D7) (x : D.host.E) : star x = D.conjF x := by
  rw [D.conjF_eq]
  have := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  change D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj]
  exact (D.host.conjE_apply D.host.φ₀ x).symm

theorem one_mem_dd (D : Formalism.BasicNotions.D7) (k : ℕ) :
    (1 : D.host.E) ∈ ((ddS D) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have h0 : ddS D ≠ 0 := by
    unfold ddS
    rw [FractionalIdeal.coeIdeal_ne_zero]
    exact Ideal.map_ne_bot_of_ne_bot (differentIdeal_ne_bot)
  have hle : ddS D ≤ 1 := by
    unfold ddS
    exact FractionalIdeal.coeIdeal_le_one
  have hk0 : ddS D ^ k ≠ 0 := pow_ne_zero _ h0
  have hk1 : ddS D ^ k ≤ 1 := pow_le_one' hle k
  rw [zpow_neg, zpow_natCast]
  have h1 := FractionalIdeal.inv_anti_mono hk0 hk1
  rw [inv_one] at h1
  exact h1 (FractionalIdeal.one_mem_one _)

theorem pair_int (D : Formalism.BasicNotions.D7) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hU : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ)
    {x y : (VS D).V} (hx : x ∈ Λ) (hy : y ∈ Λ) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = (VS D).hT x y := by
  have hd : y ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by rw [hU]; exact hy
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at hd
  rw [Submodule.mem_iInf] at hd
  have hd2 := hd x
  rw [Submodule.mem_iInf] at hd2
  have hint := hd2 hx
  rw [Submodule.mem_comap] at hint
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 hint
  simp only [LinearMap.coe_restrictScalars] at ho
  exact ⟨o, ho⟩

theorem modG_at (D : Formalism.BasicNotions.D7) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {y : (VS D).V}
    (h : ModG (VS D) Λ (gS D) y) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ l ∈ Λ, (s : D.host.E) • y = ((gS D : ℕ) : D.host.E) • l := by
  obtain ⟨s, hs, hsy⟩ := h P hP
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hsy
  obtain ⟨l, hl, hl'⟩ := hsy
  refine ⟨s, hs, l, hl, ?_⟩
  rw [algebraMap_smul, ← hl', ← algebraMap_smul (A := D.host.E) ((gS D : ℕ) : 𝓞 D.host.E) l]
  simp

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

def sg1 (p : PlF D) (g : Loc.SplitG (M p).L) : D.host.E →+* (D.s.atP p).Fp :=
  (RingHom.fst _ _).comp (g.e.toRingEquiv.toRingHom.comp (D.s.atP p).ιE)

def sg2 (p : PlF D) (g : Loc.SplitG (M p).L) : D.host.E →+* (D.s.atP p).Fp :=
  (RingHom.snd _ _).comp (g.e.toRingEquiv.toRingHom.comp (D.s.atP p).ιE)

theorem firstSplitEmbed_apply (p : PlF D) (g : Loc.SplitG (M p).L) (x : D.host.E) :
    sg1 p g x = (g.e ((D.s.atP p).ιE x)).1 := rfl

theorem secondSplitEmbed_apply (p : PlF D) (g : Loc.SplitG (M p).L) (x : D.host.E) :
    sg2 p g x = (g.e ((D.s.atP p).ιE x)).2 := rfl

theorem firstSplitEmbed_star (δ : ∀ p : PlF D, (D.s.atP p).Fp) (hA : ∀ p, Agree δ M p) (p : PlF D) (g : Loc.SplitG (M p).L)
    (x : D.host.E) : sg1 p g (star x) = sg2 p g x := by
  have hcj : (M p).L.cj = (D.s.atP p).cj := (hA p).2.2.1
  rw [firstSplitEmbed_apply, secondSplitEmbed_apply, star_eq_conjF]
  have h1 : (D.s.atP p).ιE (D.conjF x) = (D.s.atP p).cj ((D.s.atP p).ιE x) := ((D.s.atP p).cj_ιE x).symm
  rw [h1, ← hcj, g.e_cj]
  rfl

theorem split_ell (δ : ∀ p : PlF D, (D.s.atP p).Fp) (hA : ∀ p, Agree δ M p) (p : PlF D) (g : Loc.SplitG (M p).L)
    (hs : (M p).split = some g) :
    (g.q : (D.s.atP p).Fp) = ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ∧
      Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
  have hm := (hA p).2.2.2.2.2
  rw [hs] at hm
  rcases hsp : (D.s.atP p).split with _ | sg
  · rw [hsp] at hm
    exact hm.elim
  · rw [hsp] at hm
    have hqq : g.q = sg.q := hm.2
    refine ⟨by rw [hqq, sg.q_eq], (D.s_split p).1 (by rw [hsp]; rfl)⟩

theorem val_q_lt (p : PlF D) (g : Loc.SplitG (M p).L) :
    valuation (D.s.atP p).Fp (g.q : (D.s.atP p).Fp) < 1 :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 g.q_irr.not_isUnit

theorem gS_split (p : PlF D) (h : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)) :
    ∃ k : ℕ, gS D = Loc.resChar p * k := by
  unfold gS
  rcases Finset.mem_insert.1 h with h0 | h1
  · exact ⟨D.host.g 1, by rw [h0]⟩
  · exact ⟨D.host.g 0, by rw [Finset.mem_singleton.1 h1, mul_comm]⟩

theorem cong_one {K : Type} [Field K] [ValuativeRel K] (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hU : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ) {x y : (VS D).V} (hx : x ∈ Λ) (hy : ModG (VS D) Λ (gS D) y)
    (σ : D.host.E →+* K) (P : HeightOneSpectrum (𝓞 D.host.E)) (hgP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (hPσ : ∀ s : 𝓞 D.host.E, s ∉ P.asIdeal → valuation K (σ (s : D.host.E)) = 1) (q m : 𝒪[K])
    (hg : ((gS D : ℕ) : K) = (q : K) * m) : ∃ t : 𝒪[K], σ ((VS D).hT x y) = (q : K) * t := by
  obtain ⟨s, hs, l, hl, hsl⟩ := modG_at D Λ hy P hgP
  obtain ⟨o, ho⟩ := pair_int D Λ hU hx hl
  have he : (s : D.host.E) * (VS D).hT x y = ((gS D : ℕ) : D.host.E) * o := by
    rw [ho, ← smul_eq_mul, ← map_smul, hsl, map_smul, smul_eq_mul]
  obtain ⟨t, ht⟩ := div_q σ q m 1 (gS D) (s : D.host.E) _ o (hPσ s hs) (by rw [pow_one]; exact hg) he
  exact ⟨t, by rw [ht, pow_one]⟩

theorem cong_two {K : Type} [Field K] [ValuativeRel K] (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hU : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ) {y y' : (VS D).V} (hy : ModG (VS D) Λ (gS D) y)
    (hy' : ModG (VS D) Λ (gS D) y') (σ : D.host.E →+* K) (P P' : HeightOneSpectrum (𝓞 D.host.E))
    (hgP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (hgP' : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal)
    (hPσ : ∀ s : 𝓞 D.host.E, s ∉ P.asIdeal → valuation K (σ (s : D.host.E)) = 1)
    (hP'σ : ∀ s : 𝓞 D.host.E, s ∉ P'.asIdeal → valuation K (σ (star (s : D.host.E))) = 1) (q m : 𝒪[K])
    (hg : ((gS D : ℕ) : K) = (q : K) * m) : ∃ t : 𝒪[K], σ ((VS D).hT y y') = (q : K) ^ 2 * t := by
  obtain ⟨s, hs, l, hl, hsl⟩ := modG_at D Λ hy P' hgP'
  obtain ⟨s', hs', l', hl', hsl'⟩ := modG_at D Λ hy' P hgP
  obtain ⟨o, ho⟩ := pair_int D Λ hU hl hl'
  have he : (star (s : D.host.E) * s') * (VS D).hT y y' = ((gS D ^ 2 : ℕ) : D.host.E) * o := by
    have h1 : (VS D).hT ((s : D.host.E) • y) ((s' : D.host.E) • y') = star (s : D.host.E) * s' * (VS D).hT y y' := by
      rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
      ring
    have h2 : (VS D).hT (((gS D : ℕ) : D.host.E) • l) (((gS D : ℕ) : D.host.E) • l') =
        ((gS D ^ 2 : ℕ) : D.host.E) * (VS D).hT l l' := by
      rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply,
        star_natCast]
      push_cast
      ring
    rw [← h1, hsl, hsl', h2, ho]
  have hc : valuation K (σ (star (s : D.host.E) * s')) = 1 := by
    rw [map_mul, Valuation.map_mul, hP'σ s hs, hPσ s' hs', one_mul]
  obtain ⟨t, ht⟩ := div_q σ q (m ^ 2) 2 (gS D ^ 2) _ _ o hc (by push_cast; rw [hg]; ring) he
  exact ⟨t, ht⟩

theorem fin_three {E K : Type} [Field E] [Field K] (σ : E →+* K) (A B C : E) (T T' : ℕ) (c : Prop) [Decidable c]
    (hA : A = if c then -(T : E) else 0) (hB : B = if c then -(T' : E) else 0) (x : K) (hx : σ C = x) :
    σ (A + B - C) + (if c then (T : K) + (T' : K) else 0) = -x := by
  rw [map_sub, map_add (f := _), hx, hA, hB]
  split_ifs
  · rw [map_neg, map_neg, map_natCast, map_natCast]
    ring
  · rw [map_zero]
    ring

end PI.CntNotIntW
end
end
