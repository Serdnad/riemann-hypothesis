module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.Bundle002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle053
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Formalism.HermitianLattices.Bundle001
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.integral_periodic_compactSupport_eq_finiteSum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (ϖ : kˣ), GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (A B : ℕ) (T : Finset k), (∀ t ∈ T, valuation k t ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k)) → (∀ x : k, valuation k x ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) → ∃! t, t ∈ T ∧ valuation k (x - t) ≤ valuation k ((ϖ : k) ^ B)) → ∀ (I : Type) [Fintype I] [DecidableEq I] (F : (I → k) → ℂ), (∀ x, F x ≠ 0 → ∀ i, valuation k (x i) ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k)) → (∀ x y, (∀ i, valuation k (y i) ≤ valuation k ((ϖ : k) ^ B)) → F (x + y) = F x) → ∫ x, F x ∂(Measure.pi fun _ : I => ν) = (((resCard k : ℂ) ^ B)⁻¹) ^ Fintype.card I * ∑ t ∈ Fintype.piFinset (fun _ : I => T), F t := by
  first | exact @GlobalTheory.PeriodicIntegral.integral_eq_sum | exact GlobalTheory.PeriodicIntegral.integral_eq_sum | (intros; apply GlobalTheory.PeriodicIntegral.integral_eq_sum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX

namespace GlobalTheory

theorem cloud_add_node_le_ten_b : ∀ (C : Formalism.MainNotions.Inhab.FC) (cD ch : ℝ) (D : D7) (L : SizeData₂ D), Val C cD ch L →
    SizesAt L → L.sc.x ≤ L.sc.X' → ∀ τ : D.what₂.Tau,
    (∀ i j, (((D.hc τ).v i : ℚ) : ℝ) + (((D.hc τ).b j : ℚ) : ℝ) ≤ 10 * L.sc.b) ∧
      ∀ j j', (((D.hc τ).b j' : ℚ) : ℝ) - (((D.hc τ).b j : ℚ) : ℝ) ≤ 10 * L.sc.b := by
  intro C cD ch D L hV hS hxX τ
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -, -, -, -, -, hDel, -, hBm, -⟩ := hS
  obtain ⟨hv, -, ⟨b1, hbj, htop, hthick, hthin⟩, -⟩ := hV.hc
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL : 0 < L.sc.L := Real.rpow_pos_of_pos hx0 _
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp hL.le
  have hX'pos : 0 < L.sc.X' := Real.exp_pos _
  have hb'0 : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a; positivity
  have hb'b : L.sc.b' ≤ L.sc.b := by
    unfold Scale.b' Scale.a
    rw [div_le_iff₀ hX'pos]
    nlinarith
  have hwb : L.sc.w'' D.R.n ≤ L.sc.b := by
    unfold Scale.w''
    rcases Nat.eq_zero_or_pos D.R.n with hn | hn
    · simp [hn]; linarith
    · have h1 : (1:ℝ) ≤ D.R.n := by exact_mod_cast hn
      have : (1:ℝ) ≤ L.sc.x * D.R.n := by nlinarith
      exact (div_le_self hb'0 this).trans hb'b

  have hw : ((NumberField.Units.torsionOrder D.host.E : ℕ) : ℝ) ≤ L.sc.b := by
    have h1 := UpperTheory.Mu.host_torsionOrder_le D.host
    have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
    have hkN : D.R.k ≤ D.R.N D.R.m := Nat.le_add_right _ _
    have hm2 := D.R.two_le_m
    have hm10 : 8 ≤ D.R.m ^ 10 := le_trans (by norm_num) (Nat.pow_le_pow_left hm2 10)
    have h2 : NumberField.Units.torsionOrder D.host.E ≤ D.R.k * (D.R.N D.R.m * D.R.m ^ 10) := by
      calc _ ≤ 8 * D.R.f ^ 2 := h1
        _ = D.R.f * (D.R.f * 8) := by ring
        _ ≤ _ := Nat.mul_le_mul hfk (Nat.mul_le_mul (hfk.trans hkN) hm10)
    have h3 : ((NumberField.Units.torsionOrder D.host.E : ℕ) : ℝ) ≤
        (D.R.k : ℝ) * ((D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10) := by exact_mod_cast h2
    have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have h4 := mul_le_mul_of_nonneg_left hDel.1 hk0
    have hD := hDel.2.2.2.2.1
    have hth : (1 : ℝ) ≤ L.sc.x ^ szTh L :=
      Real.one_le_rpow hx.le (by unfold szTh; linarith [L.sc.eps_pos])
    have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    have h5 : (1 : ℝ) ≤ L.sc.x ^ szTh L * D.R.m := by nlinarith
    have hkD0 : (0 : ℝ) ≤ (D.R.k : ℝ) * (D.s.Del : ℝ) := le_trans (by positivity) h4
    have h6 := le_mul_of_one_le_left hkD0 h5
    have e : (L.sc.x ^ szTh L * D.R.m) * ((D.R.k : ℝ) * (D.s.Del : ℝ)) =
        L.sc.x ^ szTh L * D.R.m * D.R.k * (D.s.Del : ℝ) := by ring
    linarith

  have hbase : ((b1 τ : ℤ) : ℝ) ≤ 3 * L.sc.b := by
    by_cases htp : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htp
      have h1 := htop τ ⟨t, ht⟩ hte.symm
      have h2 := hBot ⟨t, ht⟩
      have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_pos_of_pos hx0 _).le hLa.1
      have hsec : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k := by
        have := Real.log_nonneg hx.le
        have := Real.rpow_pos_of_pos hx0 (szTh L)
        positivity
      have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
      have hq : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
        have : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
            4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
        unfold SizeRho at hRho
        linarith
      have hq' : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k ≤ L.sc.b' / 4 := by
        have : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
            (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
        rw [this]; nlinarith
      have hfl : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' :=
        (Int.floor_le _).trans (div_le_self hb'0 hx.le)
      have : ((b1 τ : ℤ) : ℝ) = (L.bT ⟨t, ht⟩ : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) := by
        rw [h1]; push_cast; ring
      linarith
    · by_cases hth : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · have hc := Int.ceil_lt_add_one L.sc.b
        have h := (hthick τ hth).2
        have hR : ((b1 τ : ℤ) : ℝ) < ((⌈L.sc.b⌉ : ℤ) : ℝ) + ((NumberField.Units.torsionOrder D.host.E : ℕ) : ℝ) := by
          exact_mod_cast h
        linarith
      · have h := hthin τ ⟨(D.eTau τ).2, htp, hth⟩
        have hc := Int.ceil_lt_add_one (L.sc.w'' D.R.n)
        rw [h]; linarith

  have hbR : ∀ j : Fin D.R.m, (((D.hc τ).b j : ℚ) : ℝ) = (b1 τ : ℝ) + (j.1 : ℝ) * (h0v L.sc ch : ℝ) := by
    intro j; rw [(hbj τ j).1]; push_cast; ring
  have hh0 : (0 : ℝ) ≤ (h0v L.sc ch : ℝ) := Nat.cast_nonneg _
  have hspan : ∀ j : Fin D.R.m, (j.1 : ℝ) * (h0v L.sc ch : ℝ) ≤ (b1 τ : ℝ) := by
    intro j
    have hm : 0 < D.R.m := j.pos
    have hB := hBm τ hm
    rw [hbR, hbR] at hB
    have hj : (j.1 : ℝ) ≤ ((D.R.m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : j.1 ≤ D.R.m - 1)
    have := mul_le_mul_of_nonneg_right hj hh0
    simp only [Nat.cast_zero, zero_mul, add_zero] at hB
    linarith
  refine ⟨fun i j => ?_, fun j j' => ?_⟩
  · have hm : 0 < D.R.m := j.pos
    rw [hv τ i, hbR j]
    have hD := hDel.2.2.2.2.1
    rw [hV.Del_eq] at hD
    simp only [Rat.cast_natCast] at hD
    have hth : (1 : ℝ) ≤ L.sc.x ^ szTh L :=
      Real.one_le_rpow hx.le (by unfold szTh; linarith [L.sc.eps_pos])
    have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast hm
    have hDl0 : (0 : ℝ) ≤ (Delv L.sc cD : ℝ) := Nat.cast_nonneg _
    have hkD0 : (0 : ℝ) ≤ (D.R.k : ℝ) * (Delv L.sc cD : ℝ) := by positivity
    have hkD : (D.R.k : ℝ) * (Delv L.sc cD : ℝ) ≤ L.sc.b := by
      have h1 : (1 : ℝ) ≤ L.sc.x ^ szTh L * D.R.m := by nlinarith
      have : (D.R.k : ℝ) * (Delv L.sc cD : ℝ) ≤ (L.sc.x ^ szTh L * D.R.m) * ((D.R.k : ℝ) * (Delv L.sc cD : ℝ)) := by
        nlinarith
      have e : (L.sc.x ^ szTh L * D.R.m) * ((D.R.k : ℝ) * (Delv L.sc cD : ℝ)) =
          L.sc.x ^ szTh L * D.R.m * D.R.k * (Delv L.sc cD : ℝ) := by ring
      linarith
    have hki : ((D.R.k - 2 - i.1 : ℕ) : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast (by omega : D.R.k - 2 - i.1 ≤ D.R.k)
    simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
    have := mul_le_mul_of_nonneg_right hki (by positivity : (0:ℝ) ≤ 4 * (Delv L.sc cD : ℝ))
    have := hspan j
    nlinarith
  · rw [hbR j, hbR j']
    have h1 := hspan j'
    have h2 : 0 ≤ (j.1 : ℝ) * (h0v L.sc ch : ℝ) := by positivity
    linarith

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.TwBridge

theorem idxIsProd_of_ok : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → IdxIsProd sel mu s L := by
  intro X Pr R Ch sel S₀ mu cst L G s hL hP j hj hh hex
  have hrefl : ∀ (i : ℕ) (P : rowSG Pr sel mu) (a : AutY X R i), SameDC (Pr := Pr) cst.sharp i P.1 a a :=
    fun i P a => ⟨1, one_mem _, 1, one_mem _, by simp⟩
  rcases j with _ | i
  · obtain ⟨b, hb⟩ := hL.zero_uniq
    refine ⟨b, fun P => ?_, fun b' _ => hb b'⟩
    obtain ⟨b₀, hb₀⟩ := hex P
    rw [← hb₀, hL.zero_h, hL.zero_h]
  · have hi : i < s := by omega
    choose bP hbP using hex
    obtain ⟨b, hb⟩ := hL.surj i hi hh
      (fun P hPg => hbP P ▸ hL.stabG (i + 1) (bP P) P hPg)
      (fun P hPg => hbP P ▸ hL.boundQ (i + 1) (bP P) P hPg)
      (fun P => by
        obtain ⟨al, hal⟩ := hL.nonvan i hi (bP P) P
        exact ⟨al, hbP P ▸ hal⟩)
    refine ⟨b, fun P => ?_, fun b' hb' => ?_⟩
    · have h1 := hb P
      rw [← hbP P] at h1 ⊢
      exact hP (i + 1) b (bP P) P h1
    · refine hL.inj i hi b' b (fun P => ?_)
      have e : L.h (i + 1) b' P = L.h (i + 1) b P := by
        have h1 := hb P
        rw [hb' P, ← hbP P] at *
        exact (hP (i + 1) b (bP P) P h1).symm
      rw [e]; exact hrefl _ _ _

end GlobalTheory.TwBridge
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridge.ZeroReps
open GlobalTheory.SymBridge

theorem toLoc_id {X : Fields} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : X.E →+* k) {A : Type} [DecidableEq A] {n : ℕ} (e : A ≃ Fin n) :
    toLoc ι e e (LinearMap.id : (Fin n → X.E) →ₗ[X.E] (Fin n → X.E)) = 1 := by
  ext i j
  simp only [toLoc, LinearMap.id_apply, Pi.single_apply, Matrix.one_apply, e.injective.eq_iff]
  split_ifs <;> simp

theorem exists_isOrdY_zero (R : Ranks) (c : ℕ) (hc : c = cOf R 0) :
    ∃ e : XIx (Fin R.k) (Fin R.t) 0 ⊕ Fin c ≃ Fin (R.N 0 + cOf R 0), IsOrdY e := by
  classical
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have hb : ∀ a : XIx (Fin R.k) (Fin R.t) 0 ⊕ Fin c, yPos xPos (R.N 0) a < R.N 0 + cOf R 0 := by
    rintro (((i | i) | p) | i)
    · simp only [yPos, Sum.elim_inl, xPos]; omega
    · exact i.elim0
    · exact p.1.elim0
    · simp only [yPos, Sum.elim_inr]; omega
  let f : XIx (Fin R.k) (Fin R.t) 0 ⊕ Fin c → Fin (R.N 0 + cOf R 0) := fun a => ⟨yPos xPos (R.N 0) a, hb a⟩
  have hf : Function.Bijective f := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
    · rintro (((i | i) | p) | i) (((i' | i') | p') | i') hh <;>
        simp only [f, Fin.mk.injEq, yPos, Sum.elim_inl, Sum.elim_inr, xPos] at hh
      all_goals first
        | exact i.elim0 | exact i'.elim0 | exact p.1.elim0 | exact p'.1.elim0
        | (congr 1; first | (congr 2; exact Fin.ext hh) | exact Fin.ext (by omega))
        | omega
    · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      rw [hN]; omega
  exact ⟨Equiv.ofBijective f hf, fun a => rfl⟩

theorem reps_zero : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → _root_.GlobalTheory.TwBridge.AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), _root_.Formalism.L2.Col.ChIdx.Ok Ch sel mu cst L G s → IdxProd sel mu cst L → ∀ c (h : 0 + c = s), {g : GL (XIx (Fin R.k) (Fin R.t) (0) ⊕ Fin (c + 1)) k | ∃ b : L.β 0, IsGL ι (L.h 0 b P) g} = {1} := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν _ _ hA L G hL _ c h
  have hm : R.m = s + 2 := hA.steps
  have hcO : c + 1 = cOf R 0 := by unfold cOf; omega
  obtain ⟨b₀, -⟩ := hL.zero_uniq
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨b, e, -, hg⟩
    rw [hL.zero_h] at hg
    apply Units.ext
    rw [hg]
    exact toLoc_id ι e
  · rintro rfl
    obtain ⟨e, he⟩ := exists_isOrdY_zero R (c + 1) hcO
    refine ⟨b₀, e, he, ?_⟩
    rw [hL.zero_h]
    exact (toLoc_id ι e).symm

end GlobalTheory.TwBridge.ZeroReps
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.TwBridge.TopPhi

theorem topPhi : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e → ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)),
      (W.T s R).PhiTop (fromCols (toLoc ι e e' y).toRows₁ 0) =
        σ₀ (PhiTop Ch mu cst.sharp s P.1 (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))))) := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hA hPhi e' e he' he y
  have hm : R.m = s + 2 := hA.steps
  have hlast : (e (Sum.inr ())).val = R.N R.m - 1 := he (Sum.inr ())
  have hc : cOf R (s + 1) = 0 := by unfold cOf; omega
  let E1' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (Equiv.sumEmpty _ _).trans (e'.trans (finCongr (by omega)))
  have hbd : ∀ z, (e (Sum.inl z)).val < R.N R.m - 1 + 0 := fun z => by
    have h1 := (e (Sum.inl z)).isLt
    have h2 : e (Sum.inl z) ≠ e (Sum.inr ()) := e.injective.ne (by simp)
    have h3 : (e (Sum.inl z)).val ≠ R.N R.m - 1 := fun h => h2 (Fin.ext (h.trans hlast.symm))
    omega
  let f1 : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) → Fin (R.N R.m - 1 + 0) :=
    fun z => ⟨(e (Sum.inl z)).val, hbd z⟩
  have hf1 : Function.Bijective f1 := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun z z' h => ?_, ?_⟩
    · have h' := Fin.val_eq_of_eq h
      have : e (Sum.inl z) = e (Sum.inl z') := Fin.ext h'
      exact Sum.inl_injective (e.injective this)
    · have := Fintype.card_congr e
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_unit, Fintype.card_fin] at this ⊢
      omega
  let E1 := Equiv.ofBijective f1 hf1
  have hE1' : IsOrdY E1' := by
    rintro (a | a)
    · exact he' a
    · exact a.elim0
  have hE1 : IsOrd zPos E1 := fun z => he (Sum.inl z)
  have hmat : fromCols (toLoc ι e e' y).toRows₁ 0 =
      toLoc ι E1 E1' (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1)))) := by
    ext z c
    rcases c with c | c
    · simp only [fromCols_apply_inl, toRows₁_apply, toLoc, LinearMap.comp_apply, prXp, LinearMap.funLeft_apply]
      have hs : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))) (Pi.single (E1' (Sum.inl c)) 1) =
          Pi.single (e' c) 1 := by
        funext i
        simp [E1', Pi.single_apply, Fin.ext_iff]
      rw [hs]
      rfl
    · exact c.elim0
  rw [hmat]
  exact hPhi.2 E1' E1 hE1' hE1 _

end GlobalTheory.TwBridge.TopPhi
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.MRepsPick

theorem exists_rep_of_bounds : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (γ : AutY X R (j + 1)), (∀ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1, γ⁻¹ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1 ∧ ((qOf P.1 : X.E) ^ (j + 1)) • γ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1) → (∃ al : L.β j, FiniteSumNonzeroLargeDepth Ch sel mu cst j P (L.h j al P) γ) → Nonempty (L.β (j + 1)) → ∃ b : L.β (j + 1), SameDC (Pr := Pr) cst.sharp (j + 1) P.1 (L.h (j + 1) b P) γ := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν _ _ hA L G hL _ j c h γ hγ hal hne
  classical
  obtain ⟨b₀⟩ := hne
  have hj : j < s := by omega
  let hh : rowSG Pr sel mu → AutY X R (j + 1) := fun P' => if P' = P then γ else L.h (j + 1) b₀ P'
  obtain ⟨b, hb⟩ := hL.surj j hj hh
    (by
      intro P' hP'
      have hne : P' ≠ P := by
        rintro rfl
        exact hA.nmem hP'
      simp only [hh, ite_eq_right hne]
      exact hL.stabG (j + 1) b₀ P' hP')
    (by
      intro P' hP'
      by_cases hPP : P' = P
      · subst hPP
        simp only [hh, ite_eq_left rfl]
        exact hγ
      · simp only [hh, ite_eq_right hPP]
        exact hL.boundQ (j + 1) b₀ P' hP')
    (by
      intro P'
      by_cases hPP : P' = P
      · subst hPP
        simp only [hh, ite_eq_left rfl]
        exact hal
      · simp only [hh, ite_eq_right hPP]
        exact hL.nonvan j hj b₀ P')
  refine ⟨b, ?_⟩
  have := hb P
  simpa [hh] using this

end GlobalTheory.MRepsPick
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridge.MatGL
open GlobalTheory.SymBridge

def ordY (κ τ j c n : ℕ) (h : κ + j + j * τ + c = n) : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin n :=
  ((Equiv.sumCongr ((Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv) (Equiv.refl (Fin c))).trans
    finSumFinEquiv).trans (finCongr h)

theorem ordY_isOrd (κ τ j c n : ℕ) (h : κ + j + j * τ + c = n) :
    IsOrd (yPos xPos (κ + j + j * τ)) (ordY κ τ j c n h) := by
  rintro (((i | i) | ⟨p, r⟩) | i)
  all_goals simp [ordY, yPos, xPos, finProdFinEquiv]
  all_goals ring

theorem isOrd_unique {A : Type} {n : ℕ} (pos : A → ℕ) (e e' : A ≃ Fin n) (he : IsOrd pos e) (he' : IsOrd pos e') : e = e' :=
  Equiv.ext fun a => Fin.ext ((he a).trans (he' a).symm)

variable {E k : Type} [Field E] [Field k]

theorem toLoc_eq (ι : E →+* k) {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (x : (Fin b → E) →ₗ[E] (Fin a → E)) :
    toLoc ι e e' x = ((LinearMap.toMatrix' x).submatrix e e').map ι := by
  ext i j
  simp [toLoc, LinearMap.toMatrix'_apply]

theorem toLoc_comp (ι : E →+* k) {A : Type} [Fintype A] {a : ℕ} (e : A ≃ Fin a) (x y : (Fin a → E) →ₗ[E] (Fin a → E)) :
    toLoc ι e e (x ∘ₗ y) = toLoc ι e e x * toLoc ι e e y := by
  rw [toLoc_eq, toLoc_eq, toLoc_eq, LinearMap.toMatrix'_comp, ← Matrix.submatrix_mul_equiv _ _ _ e, Matrix.map_mul]

theorem toLoc_id (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {a : ℕ} (e : A ≃ Fin a) :
    toLoc ι e e (LinearMap.id : (Fin a → E) →ₗ[E] (Fin a → E)) = 1 := by
  rw [toLoc_eq, LinearMap.toMatrix'_id, Matrix.submatrix_one_equiv, Matrix.map_one _ (map_zero ι) (map_one ι)]

def toLocGL (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {a : ℕ} (e : A ≃ Fin a) (γ : (Fin a → E) ≃ₗ[E] (Fin a → E)) :
    GL A k where
  val := toLoc ι e e γ.toLinearMap
  inv := toLoc ι e e γ.symm.toLinearMap
  val_inv := by rw [← toLoc_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, toLoc_id]
  inv_val := by rw [← toLoc_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, toLoc_id]

end GlobalTheory.TwBridge.MatGL

namespace GlobalTheory.TwBridge
open GlobalTheory.SymBridge MatGL

theorem existsUnique_isGL : ∀ (X : Fields) (R : Ranks) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (j c : ℕ), c = cOf R j → ∀ γ : AutY X R j,
    ∃! g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin c) k, IsGL ι γ g := by
  intro X R k _ _ _ _ ι j c hc γ
  subst hc
  have hN : R.k + j + j * R.t = R.N j := by simp only [Ranks.N]; ring
  have hn : R.k + j + j * R.t + cOf R j = R.N j + cOf R j := by rw [hN]
  have ho : IsOrdY (ordY R.k R.t j (cOf R j) _ hn) := by
    have := ordY_isOrd R.k R.t j (cOf R j) _ hn
    rwa [hN] at this
  refine ⟨toLocGL ι (ordY R.k R.t j (cOf R j) _ hn) γ, ⟨_, ho, rfl⟩, ?_⟩
  rintro g ⟨e, he, hg⟩
  obtain rfl := isOrd_unique _ _ _ he ho
  exact Units.ext hg

end GlobalTheory.TwBridge
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.iteratedDepthOneLevel_character_closed_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (g : (P.iter t μ hμ j).J), ∃ (g₀ : P.J) (D : Fin j → GL t k), (g₀ : GL r k).val = (g : GL (Ix r t j) k).val.submatrix Sum.inl Sum.inl ∧ (∀ i, D i ∈ KO k t ∧ (D i).val = Ix.diagonalBlockOfMatrix (g : GL (Ix r t j) k).val i) ∧ (P.iter t μ hμ j).lam g = P.lam g₀ * ∏ i : Fin j, μ (i.val + 1) (Matrix.GeneralLinearGroup.det (D i)) := by
  first | exact @GlobalTheory.SymBridge.iter_lam_closed | exact GlobalTheory.SymBridge.iter_lam_closed | (intros; apply GlobalTheory.SymBridge.iter_lam_closed <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.classicalThetaOfDatum_smul_move : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ} (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (AA : Submodule (𝓞 E) E) (SS : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ) (p : ℂ) (Ξ : Formalism.L2.Col.HomE E a b → ℂ) (θ : Formalism.L2.Ker.VV ι a b → ℂ), Formalism.L2.Ker.thC emb δ d sc AA SS N N' c (fun x => p * Ξ x) θ = Formalism.L2.Ker.thC emb δ d sc AA SS N N' c Ξ (fun z => p * θ z) := by
  first | exact @GlobalTheory.Corev.ThCLin.thC_smul_move | exact GlobalTheory.Corev.ThCLin.thC_smul_move | (intros; apply GlobalTheory.Corev.ThCLin.thC_smul_move <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Ker

theorem _root_.GlobalTheory.T.hermitian_cocycle_integral_of_local : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → ∀ x y : Formalism.L2.Col.HomE E a b, (∀ Q : HeightOneSpectrum (𝓞 E), ∃ k : E, k ≠ 0 ∧ k⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M ∧ star k • y ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ Q).asIdeal M) → (∃ n : ℤ, Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y) = n) ∧ ∃ n : ℤ, (Real.sqrt d * (HV sc (embH emb δ x) (embH emb δ y)).re + Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2 = n := by
  first | exact @GlobalTheory.CocIntLoc.integral_of_local | exact GlobalTheory.CocIntLoc.integral_of_local | (intros; apply GlobalTheory.CocIntLoc.integral_of_local <;> assumption)
end
