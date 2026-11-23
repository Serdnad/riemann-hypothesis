module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle240
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle296
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle123
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle222
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.LocalToGlobal.Columns.Bundle024
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle113
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Formalism.LocalToGlobal.UnitaryNorms.CharExGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HeckeLocalProduct.PvLocalSelf
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
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
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle202
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle119
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HeckeLocalProduct.Kernel

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV.AdInt

theorem norm_le_one_of_isIntegral' {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem intOff_of_isIntegral {K : Type} [Field K] (σ : K →+* ℂ) (S : Finset ℕ) {x : K} (hx : IsIntegral ℤ x) :
    IntOff S (σ x) := by
  have hx' : IsIntegral ℤ (σ x) := map_isIntegral_int σ hx
  have h : σ x ∈ TaylorLogMetric.Qbar := mem_algebraicClosure_iff'.2 hx'.tower_top
  refine ⟨h, fun p _ lam _ => ?_⟩
  rw [lamC_of_mem lam h]
  have h1 : IsIntegral ℤ (⟨σ x, h⟩ : TaylorLogMetric.Qbar) :=
    (isIntegral_algHom_iff ((algebraMap TaylorLogMetric.Qbar ℂ).toIntAlgHom) Subtype.val_injective).1 hx'
  exact norm_le_one_of_isIntegral' (map_isIntegral_int lam h1)

end GlobalTheory.TwV.AdInt

namespace GlobalTheory.TwV.AdInt

section Ft

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem ftY_intOff_of_psi (P : rowSG Pr sel mu) (hpsi : ∀ a, IsIntegral ℤ (cst.psi P a)) (σ : X.K →+* ℂ) {B : Finset ℕ}
    (hB : SNum B (qOf P.1)) {n : ℕ} (η : Sp X.E n →ₗ[X.E] X.E) (y : Sp X.E n) :
    IntOff B (σ (ftY sel mu cst P η y)) := by
  unfold ftY
  split_ifs
  · exact intOff_of_isIntegral σ B (hpsi _)
  · simpa using (IntOff.zero : IntOff B 0)
  · rw [map_mul, map_inv₀, map_pow, map_natCast]
    refine IntOff.mul ?_ (intOff_of_isIntegral σ B (hpsi _))
    have hB' : SNum B (qOf P.1 ^ (cst.M * n)) :=
      ⟨pow_pos hB.1 _, fun q hq hd => hB.2 q hq (hq.dvd_of_dvd_pow hd)⟩
    simpa [Nat.cast_pow] using IntOff.inv_nat hB'
  · simpa using (IntOff.zero : IntOff B 0)

end Ft

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX}

theorem xiTop_intOff_of_psi (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (hpsi : ∀ P x, IsIntegral ℤ ((t.cst μ).psi P x)) (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i)
    (Yb : Set (Sp t.X.E (D.R.N i))) (p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (i + 1))
    (x : HomE t.X.E (D.R.N i) (D.R.N (i + 1))) :
    IntOff (t.O u μ).S (t.seam.σ₀ (_root_.Formalism.L2.Col.XiTop t.Ch t.sel (t.tup μ) (t.cst μ) i p Yb p' x)) := by
  unfold _root_.Formalism.L2.Col.XiTop _root_.Formalism.L2.Col.XiTopG
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (GlobalTheory.intOff_finset_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using (IntOff.one : IntOff (t.O u μ).S 1)
    · simpa using (IntOff.zero : IntOff (t.O u μ).S 0)
  · rw [map_mul]
    refine IntOff.mul ((GlobalTheory.TopInt.phiTopG_root _ _ _ _ _ _ _ _).intOff _ _) ?_
    exact ftY_intOff_of_psi t.sel (t.tup μ) (t.cst μ) P (hpsi P) _
      (GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl Kc Y cX ex t u μ P) _ _

theorem plc_dvd_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Formalism.EigenvalueLevelCeiling.plc v ∣ n ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]

theorem g_not_mem_Qp (t : KerEntTied ex) (hsel : IsSel t.X t.sel) (hg : ∀ k, t.Pr.g k ∈ t.S) (μ : D.what₂.Tup) (k : Fin 2) :
    D.host.g k ∉ Y.Qp μ := by
  classical
  intro hk
  obtain ⟨hp, P, hPQ, hgP⟩ := (t.Q_rec μ (D.host.g k)).1 hk
  unfold QE at hPQ
  split_ifs at hPQ with h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPQ
    rw [Set.Finite.mem_toFinset] at hv
    have hgood : GoodPl t.X.E t.S v := by
      by_contra hg'
      apply hv
      have h2 := (Subgroup.mem_inf.1 (t.tup μ).2).2
      exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 v) hg'
    have hvF : ((D.host.g k : ℕ) : 𝓞 t.X.F) ∈ v.asIdeal := by
      rw [← hsel v]
      change algebraMap (𝓞 t.X.F) (𝓞 t.X.E) _ ∈ (t.sel v).asIdeal
      rw [map_natCast]
      exact hgP
    have hd := (plc_dvd_iff v _).2 hvF
    have hpl : Formalism.EigenvalueLevelCeiling.plc v = D.host.g k :=
      ((Nat.dvd_prime hp).1 hd).resolve_left fun e => by
        have h1 := (plc_dvd_iff v 1).1 (by rw [e])
        rw [Nat.cast_one] at h1
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    apply hgood.2.2
    rw [hpl, ← t.g_rec k]
    exact hg k
  · simp at hPQ

end GlobalTheory.TwV.AdInt

namespace GlobalTheory.TwV

theorem xiAd_intOff : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → ∀ i hi β β' x x' z,
    IntOff (t.O u μ).S (xiAd A a i hi β β' x x' z)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _ _ i hi β β' x x' z
  have hmu : ∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j) := fun j => ⟨_, hP.mu0 j⟩
  have hval : ∀ (j : Fin D.R.m) (v : HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) →
      t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ) := fun j v hv => by
    have h := hP.ch.muVal j v hv
    rwa [t.glob_σ] at h
  have hg : ∀ k, D.host.g k ∉ Y.Qp μ := AdInt.g_not_mem_Qp t hP.sel hP.avoid.1 μ
  unfold xiAd
  split_ifs with h
  · unfold xiPt
    split_ifs with h1 h2
    · exact GlobalTheory.KerTie.intOff_xiEntry D L hT Gi Gl Kc Y cX ex t hmu hval u μ hg i h1 _ _ _ _ _
    · subst h2
      exact GlobalTheory.xiCpl1_intOff D L hT Gi Gl Kc Y cX ex t hmu hval u μ hg _ _ _ _ _
    · exact AdInt.xiTop_intOff_of_psi t u μ hP.psi _ _ _ _ _
  · exact IntOff.zero

end GlobalTheory.TwV
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.AwayTopG

open GlobalTheory.TopStep GlobalTheory.LastSteps GlobalTheory.TopLaw

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem hom_mem_stdAt {n m : ℕ} (f : HomE E n m) (hf : ∀ j l, IntAt P (f (Pi.single j 1) l)) {v : Sp E n}
    (hv : v ∈ stdAt E n P) : f v ∈ stdAt E m P :=
  mem_stdAt.2 fun l => by
    have h := intAt_form_of_mem_stdAt (1 : E) (LinearMap.proj l ∘ₗ f) (fun i => by simpa using hf i l) hv
    simpa using h

theorem symm_mem_stdAt {n : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P) {w : Sp E n} (hw : w ∈ stdAt E n P) :
    κ.symm w ∈ stdAt E n P :=
  (hκ (κ.symm w)).1 (by rw [LinearEquiv.apply_symm_apply]; exact hw)

theorem symm_near {n D : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P)
    (hD : ∀ w ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ w - w) ∈ stdAt E n P) {w : Sp E n} (hw : w ∈ stdAt E n P) :
    ((qOf P : E) ^ D)⁻¹ • (κ.symm w - w) ∈ stdAt E n P := by
  have h := hD _ (symm_mem_stdAt hκ hw)
  rw [LinearEquiv.apply_symm_apply] at h
  have e : ((qOf P : E) ^ D)⁻¹ • (κ.symm w - w) = -(((qOf P : E) ^ D)⁻¹ • (w - κ.symm w)) := by
    rw [← smul_neg, neg_sub]
  rw [e]
  exact Submodule.neg_mem _ h

end SlopeTestRemainingChoices

theorem topDat_frames_vGs : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs →
  ∀ (κ : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))
    (κ' : Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1))),
  κ ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ w - w) ∈ stdAt t.X.E _ P.1) →
  κ' ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ' w - w) ∈ stdAt t.X.E _ P.1) →
  ∀ (y : HomE t.X.E (D.R.N (t.m2 + 1)) (D.R.N (t.m2 + 1 + 1))) (y'' : Sp t.X.E (D.R.N (t.m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y'' l)) →
  topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'') := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie P hP κ κ' hκ hκD hκ' hκ'D y y'' hy''
  have hok := t.idx_ok μ
  have hc := hok.cst_ok
  have hn : TopNum D.R (t.m2 + 1) := topNum_of (m_eq t μ)
  have hX : t.X.Ok := hPin.fields.ok
  have hPr := t.pr_ok
  have hq0 : (qOf P.1 : t.X.E) ≠ 0 := qOf_ne_zero
  obtain ⟨d, hd⟩ : ∃ d, (t.cst μ).D P = d + 1 := ⟨(t.cst μ).D P - 1, by have := hc.D_pos P; omega⟩
  by_cases hI : ∀ j l, IntAt P.1 (y (Pi.single j 1) l)
  ·
    have hA : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
        topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y (κ.symm y'') := by
      refine topDat_congr t.Ch t.sel (t.tup μ) (t.cst μ) hX hPr hc hn P hP _ _ _ ?_ ?_
      · have h1 : κ.symm ((qOf P.1 : t.X.E) • y'') ∈ stdAt t.X.E _ P.1 := symm_mem_stdAt hκ (mem_stdAt.2 hy'')
        rw [map_smul] at h1
        intro j
        simpa using mem_stdAt.1 h1 j
      · intro j
        have hkj : κ (Pi.single j 1) ∈ stdAt t.X.E _ P.1 := (hκ _).2 (single_mem_stdAt j)
        have hv : y (κ (Pi.single j 1)) ∈ stdAt t.X.E _ P.1 := hom_mem_stdAt y hI hkj
        have hz : κ'.symm (y (κ (Pi.single j 1))) ∈ stdAt t.X.E _ P.1 := symm_mem_stdAt hκ' hv
        have hzI : ∀ l, IntAt P.1 ((κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (Pi.single j 1) l) := fun l => mem_stdAt.1 hz l
        refine ⟨iff_of_true hzI (hI j), fun _ l => ?_⟩
        set s := ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ (Pi.single j 1) - Pi.single j 1) with hs
        set s' := ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ'.symm (y (κ (Pi.single j 1))) - y (κ (Pi.single j 1))) with hs'
        have hsI : s ∈ stdAt t.X.E _ P.1 := hκD _ (single_mem_stdAt j)
        have hs'I : s' ∈ stdAt t.X.E _ P.1 := symm_near hκ' hκ'D hv
        have hys : IntAt P.1 (y s l) := mem_stdAt.1 (hom_mem_stdAt y hI hsI) l
        have e1 : y s l = ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (y (κ (Pi.single j 1)) l - y (Pi.single j 1) l) := by
          rw [hs, map_smul, map_sub]
          rfl
        have e2 : s' l = ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (κ'.symm (y (κ (Pi.single j 1))) l - y (κ (Pi.single j 1)) l) := by
          rw [hs']
          rfl
        have key : (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (Pi.single j 1) l =
            y (Pi.single j 1) l + (qOf P.1 : t.X.E) * ((qOf P.1 : t.X.E) ^ d * (y s l + s' l)) := by
          rw [e1, e2, hd]
          show κ'.symm (y (κ (Pi.single j 1))) l = _
          field_simp
          ring
        rw [key, redP_add_q ((intAt_pow (intAt_nat _) d).mul (hys.add (mem_stdAt.1 hs'I l)))]
    have hB : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y (κ.symm y'') =
        topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'' := by
      unfold topDat
      congr 1
      have hw : (qOf P.1 : t.X.E) • y'' ∈ stdAt t.X.E _ P.1 := mem_stdAt.2 hy''
      have hsw := symm_near hκ hκD hw
      have hdiff : κ.symm y'' - y'' ∈ stdAt t.X.E _ P.1 := by
        refine mem_stdAt.2 fun i => ?_
        have hi := mem_stdAt.1 hsw i
        have e : (κ.symm y'' - y'') i = (qOf P.1 : t.X.E) ^ d *
            ((((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ.symm ((qOf P.1 : t.X.E) • y'') - (qOf P.1 : t.X.E) • y'')) i) := by
          rw [map_smul, hd]
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          field_simp
          ring
        rw [e]
        exact (intAt_pow (intAt_nat _) d).mul hi
      have h := ftY_comp_glint t.sel (t.tup μ) (t.cst μ) hc P (fun h => absurd hP h) (κ := 1)
        (atNL t.X.E (D.R.N (t.m2 + 1 + 1)) (D.R.N (t.m2 + 1 + 1) - 1) ∘ₗ y) y'' (κ.symm y'')
        (fun _ => hy'') (fun h => absurd hP h) (fun _ => hdiff) (fun h => absurd hP h)
      exact h
    exact hA.trans hB
  ·
    push_neg at hI
    obtain ⟨j, l, hjl⟩ := hI
    have h0 : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'' = 0 := by
      by_contra h
      exact hjl (topDat_int t.Ch t.sel (t.tup μ) (t.cst μ) hn P hP y y'' h j l)
    have h1 : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') = 0 := by
      by_contra h
      have hzI := topDat_int t.Ch t.sel (t.tup μ) (t.cst μ) hn P hP _ _ h
      apply hjl
      have hm : (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm (Pi.single j 1)) ∈ stdAt t.X.E _ P.1 :=
        hom_mem_stdAt _ hzI (symm_mem_stdAt hκ (single_mem_stdAt j))
      have e : (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm (Pi.single j 1)) = κ'.symm (y (Pi.single j 1)) := by
        simp
      rw [e] at hm
      have hm' := (hκ' _).2 hm
      rw [LinearEquiv.apply_symm_apply] at hm'
      exact mem_stdAt.1 hm' l
    rw [h0, h1]

end GlobalTheory.TwV.AwayTopG

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.TieAlgValues

theorem mem_Qbar_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ n ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [Formalism.MainNotions.TaylorLogMetric.Qbar, mem_algebraicClosure_iff, isAlgebraic_iff_isIntegral] at h ⊢
  exact IsIntegral.of_pow hn h

theorem emb_mem_Qbar {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) (k : L) : φ k ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [Formalism.MainNotions.TaylorLogMetric.Qbar, mem_algebraicClosure_iff, isAlgebraic_iff_isIntegral]
  exact (Algebra.IsIntegral.isIntegral (R := ℚ) k).map φ.toRatAlgHom

theorem conj_mem_Qbar {z : ℂ} (h : z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : (starRingEnd ℂ) z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [Formalism.MainNotions.TaylorLogMetric.Qbar, mem_algebraicClosure_iff, isAlgebraic_iff_isIntegral] at h ⊢
  exact h.map (starRingEnd ℂ).toRatAlgHom

theorem norm_mem_Qbar {z : ℂ} (h : z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : ((‖z‖ : ℝ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  refine mem_Qbar_of_pow (n := 2) (by norm_num) ?_
  have e : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * (starRingEnd ℂ) z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [e]
  exact mul_mem h (conj_mem_Qbar h)

theorem inf_mem_Qbar {L : Type} [Field L] [NumberField L] {χ : HChar L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ}
    (h : χ.HasInf φ n) (k : Lˣ) : ((χ.inf k : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [h k]
  exact prod_mem fun i _ => zpow_mem (div_mem (emb_mem_Qbar _ _) (norm_mem_Qbar (emb_mem_Qbar _ _))) _

theorem le_exp_neg_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem loc_pow_eq_one {L : Type} [Field L] [NumberField L] (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (hv : χ.TameAt v)
    (x : (v.adicCompletion L)ˣ) (hx : IsUnitAt v x) : ∃ n : ℕ, 0 < n ∧ χ.loc v x ^ n = 1 := by
  have := Formalism.UG.P.glint_finite_residueField (F := L) v
  let _ := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers L))
  set N := Fintype.card (IsLocalRing.ResidueField (v.adicCompletionIntegers L)) with hN
  have hN2 : 1 < N := Fintype.one_lt_card
  have hxO : (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx.le
  set y : v.adicCompletionIntegers L := ⟨x, hxO⟩
  have hyu : IsUnit y := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx
  have hr : IsLocalRing.residue _ y ≠ 0 := by
    rw [ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hyu
  have hp : IsLocalRing.residue _ (y ^ (N - 1) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hr, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at hp
  have hlt : Valued.v (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hp
  refine ⟨N - 1, by omega, ?_⟩
  rw [← map_pow]
  refine hv _ ?_ ?_
  · show Valued.v (((x ^ (N - 1) : (v.adicCompletion L)ˣ)) : v.adicCompletion L) = 1
    rw [Units.val_pow_eq_pow_val, map_pow, show Valued.v (x : v.adicCompletion L) = 1 from hx, one_pow]
  · have e : (((x ^ (N - 1) : (v.adicCompletion L)ˣ)) : v.adicCompletion L) - 1 =
        (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) := by
      push_cast; rfl
    rw [e]
    exact le_exp_neg_one hlt

theorem loc_mem_Qbar {L : Type} [Field L] [NumberField L] (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (hv : χ.TameAt v)
    (x : (v.adicCompletion L)ˣ) (hx : IsUnitAt v x) : ((χ.loc v x : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  obtain ⟨n, hn, h⟩ := loc_pow_eq_one χ v hv x hx
  refine mem_Qbar_of_pow hn ?_
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  exact one_mem _

end GlobalTheory.TieAlgValues

namespace GlobalTheory.TieAlgValues

open PI.HeckeProdW

theorem fin_mem_Qbar {L : Type} [Field L] [NumberField L] (χ : HChar L) (htame : ∀ v, χ.TameAt v)
    (hinf : ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (b : Ideles L) (hb : IsFinIdele b) :
    ((χ.1 b : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  classical
  obtain ⟨h, hh, hx⟩ := CharEx.classExp L
  obtain ⟨k, hk⟩ := hx b
  set u : Ideles L := b ^ h * diagUnits L k with hu
  set w : Ideles L := (infDiag k)⁻¹ * u with hw
  have hwInf : (w : AdeleRing (𝓞 L) L).1 = 1 := by
    funext pl
    show pw pl w = 1
    refine f_inv_mul (pw pl) _ _ ?_
    rw [pw_infDiag, hu, map_mul, map_pow, pw_diag]
    have : pw pl b = 1 := hb pl
    rw [this, one_pow, one_mul]
  have hwFin : ∀ v, Valued.v ((w : AdeleRing (𝓞 L) L).2 v) = 1 := by
    intro v
    show Valued.v (pv v w) = 1
    rw [hw, f_inv_mul' (pv v) _ _ (pv_infDiag v k)]
    exact hk v
  have hmemO : ∀ v : HeightOneSpectrum (𝓞 L), (w : AdeleRing (𝓞 L) L).2 v ∈ v.adicCompletionIntegers L := fun v => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact (hwFin v).le
  have hunit : ∀ v : HeightOneSpectrum (𝓞 L), IsUnit (⟨_, hmemO v⟩ : v.adicCompletionIntegers L) := fun v =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 (hwFin v)
  let y : Pu L := fun v => (hunit v).unit
  have hwy : w = Phi L y := Units.ext (Prod.ext (hwInf.trans rfl) (Subtype.ext (funext fun v => rfl)))
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring χ
  set p : Pu L := ∏ v ∈ T, Pi.mulSingle v (y v) with hp
  have hpv : ∀ v ∈ T, p v = y v := fun v hv => by
    rw [hp, Finset.prod_apply, Finset.prod_pi_mulSingle, if_pos hv]
  have hsplit : y = p * (p⁻¹ * y) := by rw [mul_inv_cancel_left]
  have hrest : χ.1 (Phi L (p⁻¹ * y)) = 1 :=
    hT _ fun v hv => by rw [Pi.mul_apply, Pi.inv_apply, hpv v hv, inv_mul_cancel]
  have hwQ : ((χ.1 w : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    rw [hwy, hsplit, map_mul, map_mul, hrest, mul_one, hp, map_prod, map_prod, Units.coe_prod]
    refine prod_mem fun v _ => ?_
    rw [Phi_single]
    refine loc_mem_Qbar χ v (htame v) _ ?_
    show Valued.v (((y v : v.adicCompletionIntegers L) : v.adicCompletion L)) = 1
    exact hwFin v
  have hue : u = infDiag k * w := by rw [hw, mul_inv_cancel_left]
  have hχu : χ.1 u = χ.1 b ^ h := by rw [hu, map_mul, χ.2.2 k, mul_one, map_pow]
  refine mem_Qbar_of_pow hh ?_
  rw [← Units.val_pow_eq_pow_val, ← hχu, hue, map_mul, Units.val_mul]
  exact mul_mem (hinf k) hwQ

end GlobalTheory.TieAlgValues

namespace GlobalTheory.TieAlgValues

open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

def finIdele {L : Type} [Field L] [NumberField L] (z : (FiniteAdeleRing (𝓞 L) L)ˣ) : Ideles L :=
  MulEquiv.prodUnits.symm (1, z)

theorem mt_mem_Qbar : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m,
    ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar) := by
  intro D _ _ _ _ _ _ _ _ t u μ _ A dtU _ hP _ i hi y
  obtain ⟨x, hx⟩ := hP.q_read.1 (dtU y)
  obtain ⟨ι, hι⟩ := exists_isAdIso t.X.F t.X.E
  set b : Ideles t.X.E := finIdele (Units.map ι.toRingHom.toMonoidHom x) with hbdef
  have hb : IsFinIdele b := fun _ => rfl
  have hbx : ι (x : AfE t.X.F t.X.E) = (b : AdeleRing (𝓞 t.X.E) t.X.E).2 := rfl
  have key : ((D.muTil (i + 1) (A.q x) : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar := by
    rw [hP.muTil ι hι ⟨i, hi⟩ b x hb hbx]
    obtain ⟨n, -, hn⟩ := (hP.mu0 ⟨i, hi⟩).inf
    exact fin_mem_Qbar _ (hP.mu0 ⟨i, hi⟩).tame (inf_mem_Qbar hn) b hb
  by_cases hμ : μ = D.what₂.mu0
  · rw [(hP.ref hμ).2, ← hx]
    exact key
  · obtain ⟨ξ, hξ, hmt⟩ := hP.tw μ hμ rfl
    have e : (t.O u μ).mt (i + 1) = D.muTil (i + 1) * ξ := by
      rw [hmt u]
      exact if_pos (⟨by omega, by omega⟩ : 1 ≤ i + 1 ∧ i + 1 ≤ D.R.m)
    rw [e, MonoidHom.mul_apply, Units.val_mul, ← hx]
    refine mul_mem key ?_
    rw [hξ x, Units.coe_map]
    exact emb_mem_Qbar _ _

end GlobalTheory.TieAlgValues
end
end
