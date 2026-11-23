module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetDiagonalBlockActsByInfinitesimalCharac
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle601
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle611
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle557
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle561
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle605
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle607
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjRes

section General

variable {D : D7}

theorem locK_conj {c c' : (AE D)ˣ →* Circle} {χ χ' : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ')
    (τ : ℂ ≃+* ℂ) (hc : ∀ x, ((c' x : Circle) : ℂ) = τ ((c x : Circle) : ℂ)) (P : Pl D.host.E) (k : D.host.Eˣ) :
    ((χ'.locK P k : ℂˣ) : ℂ) = τ ((χ.locK P k : ℂˣ) : ℂ) := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  rw [← h.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k), ← h'.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k), hc]

theorem exists_lift (P : Pl D.host.E) (u : (kP P)ˣ) :
    ∃ (a : 𝓞 D.host.E) (k : D.host.Eˣ), (k : D.host.E) = a ∧ (u : kP P) = Ideal.Quotient.mk _ a := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) (u : kP P)
  have : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have h0 : (a : D.host.E) ≠ 0 := by
    intro h
    have : a = 0 := by exact_mod_cast h
    rw [this, map_zero] at ha
    exact u.ne_zero ha.symm
  exact ⟨a, Units.mk0 _ h0, rfl, ha.symm⟩

theorem unrAt_of_isRes_one {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} (h : IsRes χ P 1) : χ.UnrAt P := by
  have key : ∀ (a : 𝓞 D.host.E) (k : D.host.Eˣ), (k : D.host.E) = a → a ∉ P.asIdeal → χ.locK P k = 1 := by
    intro a k hk ha
    have := P.isMaximal
    have hu : IsUnit (Ideal.Quotient.mk P.asIdeal a) := by
      let _ := Ideal.Quotient.field P.asIdeal
      exact (Ne.isUnit (fun h0 => ha (Ideal.Quotient.eq_zero_iff_mem.1 h0)))
    exact (h a k hu.unit hk rfl).symm
  refine GlobalTheory.EtaConjType.unrAt_of_locK χ P fun u hu => ?_
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer (u : D.host.E) hu.le
  have hd' : d ∉ P.asIdeal := hd
  have hd0 : (d : D.host.E) ≠ 0 := by
    intro h0
    have : d = 0 := by exact_mod_cast h0
    exact hd' (this ▸ P.asIdeal.zero_mem)
  have hn : n ∉ P.asIdeal := by
    rw [← P.valuation_eq_one_iff_notMem (K := D.host.E), ← hnd, map_mul, hu, one_mul]
    exact (P.valuation_eq_one_iff_notMem (K := D.host.E)).2 hd'
  have e1 := key d (Units.mk0 _ hd0) rfl hd'
  have e2 := key n (u * Units.mk0 _ hd0) hnd hn
  rwa [map_mul, e1, mul_one] at e2

theorem levFn_conj {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) {r : ℕ} (hr : r ≤ n) (t : ℕ) (Pg : Finset (Pl D.host.E))
    {Q Q' : Finset (Pl D.host.E)} (hQ : Q' = Q) (τ : ℂ ≃+* ℂ) (χ ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (hχ : ∀ PP ∈ Pg, ∀ x, τ ((χ PP x : ℂˣ) : ℂ) = ((χ PP x : ℂˣ) : ℂ))
    (hξ : ∀ PP ∈ Q, ∀ x, ((ξ' PP x : ℂˣ) : ℂ) = τ ((ξ PP x : ℂˣ) : ℂ)) (x) :
    ((levFn β ⟨r, hr, t, 1, Pg, Q', LevelP.triv Pg r ℂ, fun _ PP => (χ PP)⁻¹, ξ'⟩ x : ℂˣ) : ℂ) =
      τ ((levFn β ⟨r, hr, t, 1, Pg, Q, LevelP.triv Pg r ℂ, fun _ PP => (χ PP)⁻¹, ξ⟩ x : ℂˣ) : ℂ) := by
  subst hQ
  have h1 : ∀ y, ext1 (LevelP.triv Pg r ℂ).H (LevelP.triv Pg r ℂ).chi y = 1 := fun y => Lev.subgroupCharExtension_one_apply _ _
  unfold levFn
  simp only [h1, one_mul, Units.val_mul, Units.coe_prod, map_mul, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c _ => ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hχ PP hP]
  · exact Finset.prod_congr rfl fun PP hP => hξ PP hP _

theorem lev_congr (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {r : ℕ} (hr : r ≤ V.rank) (t : ℕ) (Pg : Finset (Pl D.host.E))
    {Q Q' : Finset (Pl D.host.E)} (hQ : Q' = Q) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    (levEnv V β ⟨r, hr, t, 1, Pg, Q', P, χ, ξ'⟩).J = (levEnv V β ⟨r, hr, t, 1, Pg, Q, P, χ, ξ⟩).J := by
  subst hQ
  rfl

theorem levEnv_chi (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (k : Bridge.Gf V)
    (hk : k ∈ (levEnv V β L).J) :
    (levEnv V β L).χ ⟨k, hk⟩ = levFn β (Lev.flag1L L) (Formalism.UG.bc (Lev.swapAE D) k.1) := rfl

theorem principalLevel_definite_datum_flag_eq {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (t : T0) :
    Lev.flag1L (L.datVt i t) = ⟨D.R.r, r_le_V i, D.R.t, 1, L.Pg, L.Q t, LevelP.triv L.Pg D.R.r ℂ,
      fun _ PP => (L.chi ((i : ℕ) + 1) PP)⁻¹, L.xiR t⟩ := rfl

theorem datVt_eq {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (t : T0) :
    L.datVt i t = ⟨D.R.r, r_le_V i, D.R.t, 1, L.Pg, L.Q t, (LevelP.triv L.Pg D.R.r ℂ).conj,
      fun _ PP => (L.chi ((i : ℕ) + 1) PP)⁻¹, L.xiR t⟩ := rfl

theorem lev_datVt {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) {t t' : T0} (h : L.Q t' = L.Q t) :
    (levEnv (Vc D i) (L.βV i) (L.datVt i t')).J = (levEnv (Vc D i) (L.βV i) (L.datVt i t)).J := by
  rw [datVt_eq, datVt_eq]
  exact lev_congr (Vc D i) (L.βV i) (r_le_V i) D.R.t L.Pg h _ _ (L.xiR t) (L.xiR t')

end General



theorem conj_res : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), ConjTup R τ t t' → (∀ PP ∈ R.Q t, ∀ x, ((R.xiR t' PP x : ℂˣ) : ℂ) = τ ((R.xiR t PP x : ℂˣ) : ℂ)) ∧ (∀ PP ∈ R.Q t, R.xiR t PP ≠ 1) ∧ (∀ P, (((R.xiH t').val P : ℂˣ) : ℂ) = τ (((R.xiH t).val P : ℂˣ) : ℂ)) ∧ ∀ i : Fin D.R.m, FixBase T R i τ → levJ R i t' = levJ R i t ∧ ∀ k (hk : k ∈ levJ R i t) (hk' : k ∈ levJ R i t'), (((levEnv (Vc D i) (R.βV i) (R.datVt i t')).χ ⟨k, hk'⟩ : ℂˣ) : ℂ) = τ (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨k, hk⟩ : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC τ t t' hct
  have hL := hC.lev
  have hloc := locK_conj (hL.xi t) (hL.xi t') τ hct.2
  have h1 : ∀ PP ∈ R.Q t, ∀ x, ((R.xiR t' PP x : ℂˣ) : ℂ) = τ ((R.xiR t PP x : ℂˣ) : ℂ) := by
    intro PP hP x
    obtain ⟨a, k, hk, hx⟩ := exists_lift PP x
    rw [hL.xiR t PP hP a k x hk hx, hL.xiR t' PP (hct.1 ▸ hP) a k x hk hx]
    exact hloc PP k
  refine ⟨h1, fun PP hP h => ?_, fun P => hloc P _, fun i hτ => ⟨?_, fun k hk hk' => ?_⟩⟩
  · exact (hL.Q_ram t PP).2 (Or.inl hP) (unrAt_of_isRes_one (h ▸ hL.xiR t PP hP))
  · exact lev_datVt R.toLevCh i hct.1
  · rw [levEnv_chi, levEnv_chi, principalLevel_definite_datum_flag_eq, principalLevel_definite_datum_flag_eq]
    exact levFn_conj (R.βV i) (r_le_V i) D.R.t R.Pg hct.1 τ (R.chi ((i : ℕ) + 1)) (R.xiR t) (R.xiR t') hτ.chi h1 _

end GlobalTheory.ConjRes
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.SpehInfChar GlobalTheory.BlockCap GlobalTheory.Published

namespace GlobalTheory.NormIndCap

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem tensorSp_update {c : ℕ} {n : Fin c → ℕ} (V : ∀ i, Submodule ℂ (Sm E (n i))) (i : Fin c)
    (m : ∀ j, GA E (n j)) {F : (∀ j, GA E (n j)) → ℂ} (hF : F ∈ tensorSp V) :
    ∃ θ ∈ V i, ∀ y, F (Function.update m i y) = θ.1 y := by
  classical
  let L : ((∀ j, GA E (n j)) → ℂ) →ₗ[ℂ] (GA E (n i) → ℂ) :=
    { toFun := fun F y => F (Function.update m i y), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hle : tensorSp V ≤ ((V i).map (Sm E (n i)).subtype).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, rfl⟩
    refine ⟨(∏ j ∈ Finset.univ.erase i, (φ j).1.1 (m j)) • (φ i).1, (V i).smul_mem _ (φ i).2, ?_⟩
    funext y
    change (∏ j ∈ Finset.univ.erase i, (φ j).1.1 (m j)) * (φ i).1.1 y =
      ∏ j, (φ j).1.1 (Function.update m i y j)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  obtain ⟨θ, hθ, e⟩ := hle hF
  exact ⟨θ, hθ, fun y => (congrFun e y).symm⟩

theorem qdet_block_levi {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (V : ∀ i, Submodule ℂ (Sm E (n i)))
    (τ : E →+* ℂ) (i : Fin c) (M : Multiset ℂ) (hM : HasInfCharGL (V i) τ M) (u : ℂ) (ψ : Sm E N)
    (hψ : (fun m => ψ.1 (leviEmb (Ad E) (stdBlocks n h) m)) ∈ tensorSp V) (m : ∀ j, GA E (n j)) :
    (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) =
      (M.map (u + ·)).prod * ψ.1 (leviEmb (Ad E) (stdBlocks n h) m) := by
  obtain ⟨θ, hθ, hθe⟩ := tensorSp_update V i m hψ
  have hR : restrLin (stdBlocks n h) m i ψ = θ := Subtype.ext (funext fun y => hθe y)
  have key := LinearMap.congr_fun (qdet_intertwine (restrLin (stdBlocks n h) m i) _ (Eop τ)
    (restrLin_Eop (stdBlocks n h) m i τ) (u + ((n i : ℂ) - 1) / 2)) ψ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hR] at key
  have k2 := congrArg (fun φ : Sm E (n i) => φ.1 (m i)) key
  have hc : Formalism.REAL.qdet (Eop τ) (u + ((n i : ℂ) - 1) / 2) θ = (M.map (u + ·)).prod • θ := hM.2 u θ hθ
  have hm : Function.update m i (m i) = m := Function.update_eq_self i m
  simp only [hc] at k2
  have k3 : (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) (Function.update m i (m i))) =
      (M.map (u + ·)).prod * θ.1 (m i) := k2
  rw [hm, ← hθe, hm] at k3
  exact k3

theorem hasInfCharGL_map_mulChi {a : ℕ} {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (χ : HChar E) :
    HasInfCharGL (V.map (mulChi a χ).toLinearMap) τ (m.map (· + expo χ τ)) := by
  refine ⟨by rw [Multiset.card_map]; exact h.1, ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (mulChi a χ φ) = _ • mulChi a χ φ
  rw [cap_mulChi, h.2 _ φ hφ, map_smul, Multiset.map_map]
  congr 2
  exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

end GlobalTheory.NormIndCap
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.hodgeAdaptedBasis_invariant_matrix_ratio : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), C.InvdR → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (Q : Matrix (Fin d) (Fin d) (Per.BdR l)), IsUnit Q → (∀ g : ↥(GK K), (ρ g).map (Per.zD l) * Q.map (Per.σD (g : GQ l)) = Q) → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, ∃ c c' : Matrix (Fin d) (Fin d) (Om l), (∀ i j, c i j ∈ K.1) ∧ (∀ i j, c' i j ∈ K.1) ∧ c * c' = 1 ∧ H.Q = Q * c.map C.oD := by
  first | (exact @GlobalTheory.BKLim.invMatrix_ratio) | (exact GlobalTheory.BKLim.invMatrix_ratio) | (intros; apply GlobalTheory.BKLim.invMatrix_ratio  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

namespace GlobalTheory.HodgeAt

theorem hodge_of_adapted : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (K K' : FinExt l) (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (w : Fin a → Fin a → P.R.BdR) (k : Fin a → ℤ), (∀ i j, w i j ∈ (P.PD K).Fil (k i)) → (∀ j, ∃ u : Fin a → P.R.BdR, (∀ i, u i ∈ (P.PD K).Fil (-k i)) ∧ ∑ i, u i • w i = Pi.single j 1) → (∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ i, (ρ g).map (algebraMap (Om l) P.R.BdR) *ᵥ (fun j => P.actQdR (g : GQ l) (w i j)) = w i) → ∃ H : Hodge C ξ ρ K', ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = ∑ i, if k i = n then 1 else 0 := by
  intro l _ P AI T C hFit ξ hξ K K' a ρ w k hw hspan hinv
  classical
  set ι := algebraMap (Per.BdRp l) (Per.BdR l) with hι
  obtain ⟨-, hinj, -, -⟩ := BdRField.bdR_isField l

  have hE : IsUnit (ι (aDp l ξ)) := by
    have hxiker : xi C.ε ∈ Ideal.span {ξ} := by
      rw [hξ, C.ker_theta]; exact Ideal.mem_span_singleton_self _
    obtain ⟨c0, hc0⟩ := Ideal.mem_span_singleton'.1 hxiker
    have h1 := GlobalTheory.MemLoc.TiedUnif.isUnit_xi (core_isEps l C)
    rw [← hc0, map_mul, map_mul] at h1
    exact isUnit_of_mul_isUnit_right h1

  set q : ℕ := ∑ i, (k i).natAbs with hq
  have hkq : ∀ i, 0 ≤ k i + q := by
    intro i
    have h1 : (k i).natAbs ≤ q := Finset.single_le_sum (f := fun i => (k i).natAbs) (by simp) (Finset.mem_univ i)
    omega
  set p : Fin a → ℕ := fun i => (k i + q).toNat with hp
  have hkp : ∀ i, k i + q = (p i : ℤ) := fun i => (Int.toNat_of_nonneg (hkq i)).symm

  have hV0 : ∀ i j, ∃ v : Per.BdRp l, ι (aDp l ξ) ^ q * T.eD (w j i) = ι (aDp l ξ ^ p j * v) :=
    fun i j => exists_xi_pow_mul l P AI T C ξ hξ K (k j) q (p j) (hkp j) (w j i) (hw j i)
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin a) (Fin a) (Per.BdRp l), ∀ i j, ι (aDp l ξ) ^ q * T.eD (w j i) = ι (aDp l ξ ^ p j * V i j) :=
    ⟨fun i j => Classical.choose (hV0 i j), fun i j => Classical.choose_spec (hV0 i j)⟩

  choose u hu hsum using hspan
  have hz0 : ∀ j i, ∃ z : Per.BdRp l, ι (aDp l ξ) ^ p i * T.eD (u j i) = ι (aDp l ξ ^ q * z) :=
    fun j i => exists_xi_pow_mul l P AI T C ξ hξ K (-k i) (p i) q (by have := hkp i; omega) (u j i) (hu j i)
  choose z hz using hz0
  have key : ∀ j j', ∑ i, z j i * V j' i = if j' = j then 1 else 0 := by
    intro j j'
    apply hinj
    have hs := congrFun (hsum j) j'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
    have h1 : ι (aDp l ξ) ^ q * ι (∑ i, z j i * V j' i) =
        ι (aDp l ξ) ^ q * T.eD (∑ i, u j i * w i j') := by

      rw [map_sum, map_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have ha := hV j' i
      have hb := hz j i
      simp only [map_mul, map_pow] at ha hb ⊢
      calc ι (aDp l ξ) ^ q * (ι (z j i) * ι (V j' i))
          = (ι (aDp l ξ) ^ q * ι (z j i)) * ι (V j' i) := by ring
        _ = (ι (aDp l ξ) ^ p i * T.eD (u j i)) * ι (V j' i) := by rw [hb]
        _ = T.eD (u j i) * (ι (aDp l ξ) ^ p i * ι (V j' i)) := by ring
        _ = T.eD (u j i) * (ι (aDp l ξ) ^ q * T.eD (w i j')) := by rw [ha]
        _ = ι (aDp l ξ) ^ q * (T.eD (u j i) * T.eD (w i j')) := by ring
    rw [(hE.pow q).mul_left_cancel h1, hs, Pi.single_apply]
    split_ifs <;> simp
  set N : Matrix (Fin a) (Fin a) (Per.BdRp l) := Matrix.of fun i j => z j i with hN
  have hVN : V * N = 1 := by
    ext j' j
    rw [Matrix.mul_apply, Matrix.one_apply, ← key j j']
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hN, Matrix.of_apply]; ring
  have hNV : N * V = 1 := mul_eq_one_comm.1 hVN
  refine ⟨⟨V, ⟨⟨V, N, hVN, hNV⟩, rfl⟩, p, q, Matrix.of fun i j => T.eD (w j i), fun i j => by simpa using hV i j, ?_⟩, ?_⟩
  · intro g hg
    ext r c
    have h := congrArg T.eD (congrFun (hinv g hg c) r)

    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, T.actD, hFit.o] at h
    rw [Matrix.mul_apply]
    simpa [Matrix.map_apply, Matrix.of_apply, GlobalTheory.MemLoc.Core.oD] using h
  · intro n
    have hf : (Finset.univ.filter fun i => ((p i : ℕ) : ℤ) - (q : ℤ) = n) = Finset.univ.filter fun i => k i = n := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := hkp i
      omega
    show ((Finset.univ.filter fun i => ((p i : ℕ) : ℤ) - (q : ℤ) = n).card : ℤ) = _
    rw [hf, Finset.card_filter]
    push_cast
    rfl

end GlobalTheory.HodgeAt
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

noncomputable def matCoordMap {A B : Type} [CommRing A] [CommRing B] {d : ℕ} (q : A →+* B)
    (M : Matrix (Fin d) (Fin d) B) : (Fin d → A) →ₛₗ[q] (Fin d → B) where
  toFun z := M.mulVec fun i => q (z i)
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp
  map_smul' a x := by
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp

theorem Eval.effective_of_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C), Cover h → Function.Injective (V.v h f) ∧ ∀ z : Fin d → C.A, (∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → (fun i => p.f (z i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (z i)) → ∃ y, V.v h f y = z := by
  intro l _ K bk d S B C N _ _ V h f hc
  obtain ⟨D, p, q, hpo⟩ := hc.stable.po C h
  obtain ⟨hinj, hrange⟩ := GlobalTheory.T.prism_cover_injective_and_descent l _ B C h hc
  haveI := V.fin
  haveI := V.proj
  have hcomm : p.f.comp h.f = q.f.comp h.f := congrArg Hom.f hpo.comm
  have key := GlobalTheory.T.finite_projective_module_element_descent_equalizer B.A C.A D.A h.f p.f q.f hcomm hinj (hrange D p q hpo) N (Fin d → C.A) (Fin d → D.A)
    (V.v h f) (matCoordMap p.f 1) (matCoordMap q.f (S.ε (p.comp f) (q.comp f))) (V.v (p.comp h) (p.comp f))
    (V.bc h f) (V.bc (p.comp h) (p.comp f))
    (fun x => by
      change V.v (p.comp h) (p.comp f) x = (1 : Matrix (Fin d) (Fin d) D.A).mulVec fun i => p.f (V.v h f x i)
      rw [Matrix.one_mulVec]
      funext i
      exact V.v_nat p h f x i)
    (fun x => by
      change V.v (p.comp h) (p.comp f) x = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (V.v h f x i)
      have e : ∀ a a' : Hom B D, a = a' → V.v a (q.comp f) x = V.v a' (q.comp f) x := by
        intro a a' e; subst e; rfl
      rw [V.v_ε (p.comp h) (p.comp f) (q.comp f) x, e _ _ hpo.comm]
      congr 1
      funext i
      exact V.v_nat q h f x i)
  refine ⟨key.1, fun z hz => key.2 z ?_⟩
  change (1 : Matrix (Fin d) (Fin d) D.A).mulVec (fun i => p.f (z i)) =
    (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (z i)
  rw [Matrix.one_mulVec]
  exact hz D p q hpo.comm

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EnvFF

theorem adI_map {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] {B B' : Obj l R} (f : Hom B B') (m : ℕ) :
    (adI B ^ m).map f.f = adI B' ^ m := by
  rw [Ideal.map_pow, adI, adI, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast,
    GlobalTheory.T.prism_hom_map_ideal_eq l R B B' f]

theorem ff_of_basis {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (ι : Type) [Nonempty ι]
    (h : letI := g.toAlgebra; Nonempty (Module.Basis ι R S)) : g.FaithfullyFlat := by
  letI := g.toAlgebra
  obtain ⟨b⟩ := h
  exact Module.FaithfullyFlat.of_linearEquiv _ _ b.repr

end GlobalTheory.BSP.EnvFF

open GlobalTheory.BSP.EnvFF

theorem GlobalTheory.BSP.envFF : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (t p : B.A)
    (En : Env bk B t p) (m : ℕ), (qmap En.inl m).FaithfullyFlat := by
  intro l _ K bk B t p En m
  have hJ : (adI B ^ m).map En.inl.f = adI En.Q ^ m := adI_map En.inl m
  have e : qmap En.inl m = (Ideal.quotEquivOfEq hJ).toRingHom.comp
      (Ideal.quotientMap ((adI B ^ m).map En.inl.f) En.inl.f Ideal.le_comap_map) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    rfl
  have h2 : (Ideal.quotEquivOfEq hJ).toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective (Ideal.quotEquivOfEq hJ).bijective
  have h1 : (Ideal.quotientMap ((adI B ^ m).map En.inl.f) En.inl.f Ideal.le_comap_map).FaithfullyFlat := by
    haveI : Nonempty (Digits l) := ⟨⟨0, fun _ => (Fact.out : l.Prime).pos⟩⟩
    obtain ⟨b, -⟩ := GlobalTheory.T.adicTopologicalBasis_basis_mod_pow B.A En.Q.A En.inl.f (adI B) (Digits l) En.tb m
    exact ff_of_basis _ (Digits l) ⟨b⟩
  rw [e]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _ h1 h2
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.hodgeAdaptedBasis_galois_action_bdRPlus : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K) (g : ↥(GK K)) (w : Ainf l), Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w → (ρ g).map ((aDp l).comp (Per.zA l)) * H.V.map (Per.σDp (g : GQ l)) * Matrix.diagonal (fun j => aDp l w ^ H.p j) = aDp l w ^ H.q • H.V := by
  first | (exact @GlobalTheory.BKLim.GalAdapted.gal_V) | (exact GlobalTheory.BKLim.GalAdapted.gal_V) | (intros; apply GlobalTheory.BKLim.GalAdapted.gal_V  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem isUnit_map_of_mul_eq_smul {R D : Type} [CommRing R] [CommRing D] {d : ℕ} (g : R →+* D)
    (M M' : Matrix (Fin d) (Fin d) R) (r : R) (h : M * M' = r • (1 : Matrix (Fin d) (Fin d) R)) (hr : IsUnit (g r)) :
    IsUnit (M.map g) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h2 : M.map g * M'.map g = g r • (1 : Matrix (Fin d) (Fin d) D) := by
    rw [← Matrix.map_mul, h]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h3
  exact isUnit_of_mul_isUnit_left (h3 ▸ hr.pow d)

theorem wseed_F_frob_XZ_isUnit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Ψ → IsUnit Z → IsUnit (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * (s.X.map (toDisc l (X : bk.S) bk.ρ₀) * Z).map Ψ) := by
  intro l _ K bk τ d ρ s Ψ Z hΨ hZ
  have hl := isUnit_l_disc l (X : bk.S) bk.ρ₀
  rw [Matrix.map_mul]
  refine IsUnit.mul ?_ (IsUnit.mul ?_ ?_)
  · refine isUnit_map_of_mul_eq_smul _ s.F s.F' _ s.F_mul ?_
    rw [map_pow, map_natCast]
    exact hl.pow _
  · have e : Ψ.comp (toDisc l (X : bk.S) bk.ρ₀) = (toDisc l (X : bk.S) bk.ρ₀).comp (frobS l bk.a) :=
      RingHom.ext hΨ.ext
    rw [Matrix.map_map, show (⇑Ψ ∘ ⇑(toDisc l (X : bk.S) bk.ρ₀)) = ⇑(Ψ.comp (toDisc l (X : bk.S) bk.ρ₀)) from rfl, e]
    refine isUnit_map_of_mul_eq_smul _ s.X s.X' _ s.X_mul ?_
    simp only [RingHom.comp_apply, map_mul, map_pow, map_natCast]
    exact (hl.pow _).mul ((isUnit_toDisc_frobS_E l K bk).pow _)
  · exact hZ.map (Ψ.mapMatrix)

end GlobalTheory.BKLim

end
end
