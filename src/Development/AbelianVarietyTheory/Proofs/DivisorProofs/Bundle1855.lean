module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsWt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsTr
public import Formalism.PieriBlockIdeals.Bundle003
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.MirabolicMackeyTheory.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemClosureIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle219
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle079
import Formalism.LocalToGlobal.Columns.Bundle031
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle002
public import Formalism.PieriBlockIdeals.PieriColumnMinors.ProdInitialMinorsMemDetSpan
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapNorm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.Divisibility.BrJoint
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

open Matrix

namespace GlobalTheory.BadCount.WtPsi

open Formalism.L2.SG.Pf.AllRowsWt Formalism.L2.SG.Pf.AllRowsTr

variable {g : ℕ} [Fact g.Prime] {N : ℕ} (c : ZMod g)

theorem posN_lt {a : ℕ} (h : a < N) : posN 0 N a = a := by
  unfold posN; simp [h]

theorem sdg_conj (hc : c ≠ 0) (u : Matrix (Fin N) (Fin N) (ZMod g)) :
    ∑ i ∈ Finset.range (N - 1), entN (diagonal (fun i : Fin N => (tN 0 N c i)⁻¹) * u *
      diagonal (fun i : Fin N => tN 0 N c i)) i (i + 1) = c * ∑ i ∈ Finset.range (N - 1), entN u i (i + 1) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [entN_conj, pair 0 N c hc (by rw [posN_lt (by omega), posN_lt (by omega)])]

theorem uniUp_conj (hc : c ≠ 0) (u : Matrix (Fin N) (Fin N) (ZMod g)) :
    IsUniUp (diagonal (fun i : Fin N => (tN 0 N c i)⁻¹) * u * diagonal (fun i : Fin N => tN 0 N c i)) ↔ IsUniUp u := by
  have h := PJ_conj 0 N c hc u
  unfold PJ at h
  have hv : ∀ M : Matrix (Fin N) (Fin N) (ZMod g), ∀ a, N ≤ a → a < N → entN M a N = 0 :=
    fun _ a h1 h2 => absurd h2 (by omega)
  exact ⟨fun x => (h.1 ⟨x, hv _⟩).1, fun x => (h.2 ⟨x, hv _⟩).1⟩

theorem eU_conj (hc : c ≠ 0) (ψ : AddChar (ZMod g) ℂ) :
    haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
    MonoidAlgebra.single (T 0 N c hc) 1 * eU g N ψ * MonoidAlgebra.single (T 0 N c hc)⁻¹ 1 =
      eU g N (ψ.mulShift c) := by
  classical
  have : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  unfold eU eDat
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  simp only [MonoidAlgebra.single_mul_single, one_mul, mul_one]
  refine Finset.sum_nbij' (fun u => T 0 N c hc * u * (T 0 N c hc)⁻¹) (fun v => (T 0 N c hc)⁻¹ * v * T 0 N c hc)
    ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    show IsUniUp ((T 0 N c hc * u * (T 0 N c hc)⁻¹ : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g))
    rw [← uniUp_conj c hc, ← T_conj_val 0 N c hc]
    have e : (T 0 N c hc)⁻¹ * (T 0 N c hc * u * (T 0 N c hc)⁻¹) * T 0 N c hc = u := by group
    rw [e]; exact hu
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    show IsUniUp (((T 0 N c hc)⁻¹ * v * T 0 N c hc : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g))
    rw [T_conj_val, uniUp_conj c hc]; exact hv
  · intro u _; group
  · intro v _; group
  · intro u hu
    have e : (u : GL (Fin N) (ZMod g)) = (T 0 N c hc)⁻¹ * (T 0 N c hc * u * (T 0 N c hc)⁻¹) * T 0 N c hc := by group
    have hφ : ∑ i ∈ Finset.range (N - 1), entN (u : Matrix (Fin N) (Fin N) (ZMod g)) i (i + 1) =
        c * ∑ i ∈ Finset.range (N - 1),
          entN ((T 0 N c hc * u * (T 0 N c hc)⁻¹ : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) i (i + 1) := by
      conv_lhs => rw [e]
      rw [T_conj_val, sdg_conj c hc]
    rw [hφ, AddChar.mulShift_apply]

end GlobalTheory.BadCount.WtPsi

namespace GlobalTheory.BadCount

open Formalism.L2.SG.Pf.AllRowsWt Formalism.L2.SG.Pf.AllRowsTr GlobalTheory.BadCount.WtPsi

theorem wtOf_eUk_indep : ∀ (D : D7) (k : Fin 2) (ψ ψ' : AddChar (ZMod (D.host.g k)) ℂ), ψ ≠ 1 → ψ' ≠ 1 →
    ∀ f, wtOf D k (eUk D k ψ) f = wtOf D k (eUk D k ψ') f := by
  intro D k ψ ψ' h h' f
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨c, hc0, rfl⟩ := exists_shift ψ ψ' h h'
  have hconj : eUk D k (ψ.mulShift c) =
      MonoidAlgebra.single (T 0 D.R.r c hc0) 1 * eUk D k ψ * MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1 := by
    unfold eUk
    exact (eU_conj c hc0 ψ).symm
  have h1 : (eUk D k (ψ.mulShift c) * D.ntypes.eSer k f).coeff 1 = (eUk D k ψ * D.ntypes.eSer k f).coeff 1 := by
    rw [hconj]
    have e1 : MonoidAlgebra.single (T 0 D.R.r c hc0) 1 * eUk D k ψ * MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1 *
        D.ntypes.eSer k f = MonoidAlgebra.single (T 0 D.R.r c hc0) 1 * (eUk D k ψ * D.ntypes.eSer k f) *
        MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1 := by
      rw [mul_assoc _ (MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1) (D.ntypes.eSer k f), ← D.ntypes.eSer_central,
        mul_assoc, mul_assoc, mul_assoc]
    rw [e1, tau_conj]
  have h2 : (eUk D k (ψ.mulShift c)).coeff 1 = (eUk D k ψ).coeff 1 := by
    rw [hconj, tau_conj]
  unfold wtOf
  rw [h1, h2]

end GlobalTheory.BadCount
end
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.OntoExponentsLat

variable {K : Type} [Field K] [NumberField K]

theorem natCast_notMem_of_not_dvd [StarRing K] (w : HeightOneSpectrum (𝓞 K)) {m : ℕ}
    (hm : ¬ Formalism.EigenvalueLevelCeiling.plc w ∣ m) : (m : 𝓞 K) ∉ w.asIdeal := by
  intro h
  apply hm
  have h1 : ((m : ℕ) : 𝓞 K ⧸ w.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h
  unfold Formalism.EigenvalueLevelCeiling.plc
  exact (CharP.cast_eq_zero_iff (𝓞 K ⧸ w.asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal)) m).1 h1

theorem factor_mem (w : HeightOneSpectrum (𝓞 K)) (p e n : ℕ) (ν : Fin n → ℕ)
    (hpw : ∀ m : ℕ, ¬ p ∣ m → (m : 𝓞 K) ∉ w.asIdeal) (hI : Formalism.CohomologicalDescent.LA.InclZ n n le_rfl ν p e) :
    ∀ f ∈ (Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n ν).map (toK K (Fin n × Fin n)),
      ((p : K) ^ e) • f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal
        ((Formalism.GradedWeylDivisibility.weyl (𝓞 K) n n le_rfl ν).map (toK K (Fin n × Fin n))) := by
  obtain ⟨m, hm, hmx⟩ := hI
  have hm0 : (m : K) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rintro rfl
    exact hm (dvd_zero p)
  have hval : w.valuation K ((m : K)⁻¹) ≤ 1 := by
    have h1 : w.valuation K (algebraMap (𝓞 K) K (m : 𝓞 K)) = 1 :=
      (w.valuation_eq_one_iff_notMem).2 (hpw m hm)
    rw [map_natCast] at h1
    rw [map_inv₀, h1, inv_one]
  rintro _ ⟨g, hg, rfl⟩
  rw [GlobalTheory.StdDual.dualWeyl_eq, ← GlobalTheory.StdDual.image_bidSet (Int.castRingHom (𝓞 K))] at hg
  induction hg using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨b, hb, rfl⟩ := hq
    have hbD : b ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ n n ν := by
      rw [GlobalTheory.StdDual.dualWeyl_eq]
      exact Submodule.subset_span hb
    have h1 := GlobalTheory.WeylRowAll.map_mem_weyl (Int.castRingHom (𝓞 K)) le_rfl ν _ (hmx b hbD)
    have h2 := GlobalTheory.JetOpWeylLat.smul_mem_localizationAt_of_valuation w hval (Submodule.mem_map_of_mem (f := toK K (Fin n × Fin n)) h1)
    convert h2 using 1
    rw [GlobalTheory.JetOpWeylLat.toK_map_int, GlobalTheory.JetOpWeylLat.toK_map_int, map_zsmul, ← Int.cast_smul_eq_zsmul K,
      smul_smul]
    congr 1
    push_cast
    field_simp
  | zero => simpa using zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add (f := _), smul_add]
    exact add_mem ha hb
  | smul a g _ hg =>
    rw [map_smul, smul_comm]
    exact Submodule.smul_mem _ a hg

end GlobalTheory.OntoExponentsLat

namespace GlobalTheory.OntoExponentsLat

variable {K : Type} [Field K] [NumberField K]

theorem tensor_mem (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (c : K)
    (e : ι → ℕ)
    (h : ∀ τ, ∀ f ∈ (nablaSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)),
      (c ^ e τ) • f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((delSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)))) :
    ∀ z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam),
      (c ^ ∑ τ, e τ) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  classical
  have key : ∀ y ∈ nabStd K lam, (c ^ ∑ τ, e τ) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
    intro y hy
    unfold nabStd Formalism.GradedWeylDivisibility.tensorLat at hy
    induction hy using Submodule.span_induction with
    | mem P hP =>
      obtain ⟨F, hF, rfl⟩ := hP
      choose t ht hFt using fun τ => (lc_mem_locP w _ _).1 (h τ (F τ) (hF τ))
      have hnot : (∏ τ, t τ) ∉ w.asIdeal :=
        Submonoid.prod_mem w.asIdeal.primeCompl (t := Finset.univ) (f := t) (fun τ _ => ht τ)
      refine (lc_mem_locP w _ _).2 ⟨∏ τ, t τ, hnot, ?_⟩
      have hFt' : ∀ τ, (algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ ∈
          (delSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)) := fun τ => by
        have e1 : t τ • c ^ e τ • F τ = (algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ :=
          (algebraMap_smul K (t τ) _).symm.trans (smul_smul _ _ _)
        convert hFt τ using 1
        exact e1.symm
      have hmem : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ ((algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ)) ∈ delStd K lam :=
        Submodule.subset_span ⟨_, hFt', rfl⟩
      have e2 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ ((algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ)) =
          ((algebraMap (𝓞 K) K (∏ τ, t τ)) * c ^ ∑ τ, e τ) • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (F τ) := by
        simp only [map_smul, MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod, map_mul,
          Formalism.GradedWeylDivisibility.blockEmb, MvPolynomial.rename_C]
        congr 2
        rw [← map_prod, Finset.prod_pow_eq_pow_sum]
      rw [e2] at hmem
      convert hmem using 1
      exact (algebraMap_smul K (∏ τ, t τ) _).symm.trans (smul_smul _ _ _)
    | zero => simpa using zero_mem _
    | add a b _ _ ha hb =>
      rw [smul_add]
      exact add_mem ha hb
    | smul a y _ hy =>
      have e3 : (c ^ ∑ τ, e τ) • a • y = a • (c ^ ∑ τ, e τ) • y := smul_comm _ _ _
      convert Submodule.smul_mem _ a hy using 1
      exact e3
  intro z hz
  obtain ⟨s, hs, hsz⟩ := (lc_mem_locP w _ _).1 hz
  obtain ⟨t, ht, htz⟩ := (lc_mem_locP w _ _).1 (key _ hsz)
  refine (lc_mem_locP w _ _).2 ⟨t * s, lc_mul_notMem w ht hs, ?_⟩
  convert htz using 1
  exact (mul_smul t s _).trans (congrArg (t • ·) (smul_comm s _ z))

end GlobalTheory.OntoExponentsLat

namespace GlobalTheory.OntoExponentsLat

theorem exZ_sum_smul_mem_locP_delAtr :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ)
      (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)),
      Submodule.IsFullLattice E L → ∀ (w : HeightOneSpectrum (𝓞 K)), ∀ x ∈ nabAtr emb lam L,
        (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) • x ∈
          Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delAtr emb lam L) := by
  intro E K _ _ _ _ _ ι _ n emb lam L hL w x hx
  have hM : ∀ τ, Submodule.IsFullLattice K (dualFr (tauLat emb τ L)) := fun τ =>
    du_dualFr_lattice basisAtEx _ (tauLatLattice E K ι n emb τ L hL)
  choose B hB using fun τ => basisAtEx K n _ (hM τ) w
  have hx1 : (x : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ L)) :=
    lc_le_locP w _ hx
  rw [(nabDelLoc K ι n lam _ hM w B hB).1] at hx1
  obtain ⟨z, hz, hzx⟩ := hx1
  have hfac : ∀ τ, ∀ f ∈ (nablaSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)),
      ((Formalism.EigenvalueLevelCeiling.plc w : K) ^ Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w)) • f ∈
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((delSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n))) := fun τ =>
    factor_mem w (Formalism.EigenvalueLevelCeiling.plc w) _ n (lam τ).natW (fun m hm => natCast_notMem_of_not_dvd w hm)
      (Formalism.CohomologicalDescent.LA.exact_z_specialization n n le_rfl _ (natW_antitone _) _ (Formalism.EigenvalueLevelCeiling.plc_prime w))
  have hz' := tensor_mem w lam (Formalism.EigenvalueLevelCeiling.plc w : K) _ hfac z hz
  refine (GlobalTheory.LvT.Built.ValLat.mem_localization_delAtr emb lam w hL B hB _).2 ⟨_, hz', ?_⟩
  have e1 : (actP lam B) z = (x : Pol K ι n) := hzx
  rw [map_smul, e1]
  refine (algebraMap_smul K (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^
    (∑ τ, Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) (x : Pol K ι n)).symm.trans ?_
  simp only [map_pow, map_natCast]

end GlobalTheory.OntoExponentsLat
end
end

section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.BranchNormBound

open GlobalTheory.BranchFormula GlobalTheory.BranchNorm GlobalTheory.IndefiniteRowSideFullHecke.ScaledCoisometryNorms

theorem const_le {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n} (hI : Interlace rfl lam sg) (hS : SameShift lam sg) :
    ((cBr rfl lam sg : ℤ) : ℝ) ^ 2 * kapBr ℝ rfl lam sg ≤ Formalism.MainNotions.PrimeDegreeVariant.brBd rfl lam sg ^ 2 := by
  have hx : xiBr ℂ rfl lam sg ∈ delSq ℂ (n + 1) lam := nablaSq_eq_delSq ℂ lam ▸ xi_mem hI hS
  have h := (onePlace Formalism.L2.DIV.BrJ.branching_interlacing_pairs (n + 1) n rfl lam sg hI hS).2.2.2.2.2 _ hx
  have hk : normFock lam (xiBr ℂ rfl lam sg) (xiBr ℂ rfl lam sg) = kapBr ℂ rfl lam sg := by
    rw [kapBr, normFock, fockF_eq, fockF_eq, GlobalTheory.Proof.TensorMapDescent.xiBr_map, Formalism.L2.DIV.map_extremal]
  have e1 : ((kapBr ℝ rfl lam sg : ℝ) : ℂ) = kapBr ℂ rfl lam sg := kapBr_map Complex.ofRealHom
  obtain ⟨s1, -⟩ := fockF_self_ne (f := extremal ℂ n sg) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl sg.natW)
  have h5 : normFock sg (extremal ℂ n sg) (extremal ℂ n sg) = 1 := div_self s1
  rw [brOne_xi rfl hI hS, normFock_smul, h5, hk, ← e1] at h
  simp only [map_mul, map_intCast, Complex.conj_ofReal, mul_one, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, mul_zero, zero_mul, sub_zero, add_zero] at h
  have hp := kapBr_pos hI hS
  refine le_of_mul_le_mul_right ?_ hp
  nlinarith

theorem sumGram_one (n : ℕ) : sumGram (n + 1) (1 : Matrix (Fin n) (Fin n) ℂ) 1 = 1 := by
  ext a b
  have := a.2
  have := b.2
  simp only [sumGram, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem brStd_norm_le {ι : Type} [Fintype ι] {n N : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n)
    (hI : ∀ τ, Interlace hN (Λ τ) (σ τ)) (hS : ∀ τ, SameShift (Λ τ) (σ τ)) (x : VV ℂ Λ) :
    (pairK σ (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (brStd hN Λ σ x) (brStd hN Λ σ x)).re ≤
      (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm (Λ τ) (σ τ) ^ 2) *
        (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) x x).re := by
  subst hN
  have h1 : ∀ m : ℕ, ((1 : Matrix (Fin m) (Fin m) ℂ).map (RingHom.id ℂ)).PosDef := fun m => by
    simpa using (Matrix.PosDef.one : (1 : Matrix (Fin m) (Fin m) ℂ).PosDef)
  have h := (brNorm ℂ (RingHom.id ℂ) (fun _ => rfl) ι (n + 1) n rfl Λ σ hI hS (fun _ => 1) (fun _ => h1 n)
    (fun _ => 1) (fun _ => 1) 1 one_pos (fun _ => by simp)).2.2.1 x
  simp only [nrmSq, sumGram_one, brAt, one_zpow, Finset.prod_const_one, one_smul, RingHom.id_apply, brSq, one_mul] at h
  have hp := pairK_pos (RingHom.id ℂ) (fun _ => rfl) Λ (G := fun _ => 1) (fun _ => h1 _) x
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hp)
  exact Finset.prod_le_prod₀ (fun τ _ => mul_nonneg (sq_nonneg _) (kapBr_pos (hI τ) (hS τ)).le)
    fun τ _ => const_le (hI τ) (hS τ)

end GlobalTheory.BranchNormBound
end
end

section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.FrameDepth

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem conj_mem_glLatCong {Λ Λ' : Submodule 𝒪[k] (D → k)} {u : kˣ} (G : GL D k)
    (hG : ∀ x, x ᵥ* G.val ∈ Λ' ↔ x ∈ Λ) {g : GL D k} (hg : g ∈ glLatCong u Λ') :
    G * g * G⁻¹ ∈ glLatCong u Λ := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [← hG, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← vecMul_vecMul, hg.1, hG]
  · have h1 := hg.2 _ ((hG x).2 hx)
    rw [mem_smul_lat] at h1 ⊢
    rw [← hG]
    convert h1 using 1
    rw [Units.smul_def, Units.smul_def, smul_vecMul, vecMul_vecMul, vecMul_vecMul, sub_mul, mul_sub,
      ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, mul_one, one_mul]

theorem vecMul_diagGL_mem (b c d : D → kˣ) (h : ∀ j, d j = b j * c j) (x : D → k) :
    x ᵥ* (diagGL c).val ∈ diagLat d ↔ x ∈ diagLat b := by
  refine forall_congr' fun j => ?_
  have h0 : 0 < valuation k (c j : k) := zero_lt_iff.2 (by simp)
  rw [diagGL_val, vecMul_diagonal, map_mul, h, Units.val_mul, map_mul]
  exact mul_le_mul_iff_left₀ h0

theorem mem_glLatCong_of_smul {Λ : Submodule 𝒪[k] (D → k)} {u v : kˣ} {g : GL D k}
    (hg : g ∈ glLatCong u (v • Λ)) : g ∈ glLatCong u Λ := by
  have hm : ∀ x, v • x ∈ v • Λ ↔ x ∈ Λ := fun x => by rw [mem_smul_lat, inv_smul_smul]
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [← hm, ← hm x, ← hg.1 (v • x), Units.smul_def v x, smul_vecMul, ← Units.smul_def v (x ᵥ* g.val)]
  · have h1 := hg.2 _ ((hm x).2 hx)
    rw [mem_smul_lat, mem_smul_lat] at h1
    rw [mem_smul_lat]
    convert h1 using 1
    rw [smul_comm v⁻¹, Units.smul_def v, smul_vecMul, ← Units.smul_def v, inv_smul_smul]

theorem invT_mem_of_dual {u : kˣ} {c : D → kˣ} {g : GL D k} (hg : g ∈ glLatCong u (dualLat (diagLat c))) :
    invT g ∈ glLatCong u (diagLat c) ∧ gdet (invT g) ∈ unitCong u := by
  rw [dualLat_diagLat] at hg
  have h1 := GlobalTheory.FunObj.GivenAdm.invT_mem_glLatCong (conj_mem_glLatCong (Λ := stdLat k D)
    (diagGL fun j => (c j)⁻¹) (vecMul_diagGL_mem 1 _ _ (by simp)) hg)
  have h2 : invT (diagGL fun j => (c j)⁻¹) = diagGL c := by
    rw [← _root_.inv_inj]
    refine Units.ext ?_
    rw [invT_inv_val, diagGL_val, diagonal_transpose]
    symm
    refine Units.inv_eq_of_mul_eq_one_right ?_
    simp [diagGL_val]
  rw [map_mul, map_mul, map_inv, h2] at h1
  constructor
  · have h3 := conj_mem_glLatCong (Λ := diagLat c) (diagGL c)⁻¹ (fun x => by
      rw [stdLat, ← vecMul_diagGL_mem 1 c c (by simp), vecMul_vecMul, Units.inv_mul, vecMul_one]) h1
    simpa [mul_assoc] using h3
  · have h3 := GlobalTheory.FunObj.GivenAdm.gdet_mem_unitCong h1
    rwa [gdet_mul, gdet_mul, show gdet (diagGL c)⁻¹ = (gdet (diagGL c))⁻¹ from map_inv _ _,
      mul_inv_cancel_comm] at h3

theorem HasDepth.mul_glLatCong {A : Type*} {ϖ : kˣ} {e : ℕ} {Λ : Submodule 𝒪[k] (D → k)}
    {Ψ : Matrix A D k → ℂ} (h : HasDepth ϖ e Λ Ψ) {g : GL D k} (hg : g ∈ glLatCong (ϖ ^ e) Λ)
    (Y : Matrix A D k) : Ψ (Y * g.val) = Ψ Y := by
  have hr : ∀ (M : Matrix D D k) i, (Y * M).row i = Y.row i ᵥ* M := fun M i => by
    funext j; simp [Matrix.row, Matrix.mul_apply, vecMul, dotProduct]
  by_cases hY : Y ∈ matLat A Λ
  · rw [show Y * g.val = Y + Y * (g.val - 1) by rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]]
    exact h.2 _ _ fun i => by rw [hr]; exact hg.2 _ (hY i)
  · rw [h.1 _ hY, h.1 _ fun H => hY fun i => (hg.1 _).1 (by rw [← hr]; exact H i)]

theorem hasDepth_phiA (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (A A' D : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype D] [DecidableEq D] (μ : Measure (GL A' k)) [hμ : μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ)
    (ϖ : kˣ) (e : ℕ) (c : D → kˣ) (Ψ : Matrix A' D k → ℂ) (hϖ : IsUnif ϖ) (he : 1 ≤ e) (hν : CondLE ϖ e ν)
    (hΨ : HasDepth ϖ e (diagLat c) Ψ) :
    HasDepth ϖ e (latA ϖ e (diagLat c)) (phiA μ σ ν ϖ e (diagLat c) Ψ) := by
  have hlt : valuation k ((ϖ ^ e : kˣ) : k) < 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_lt_one₀ zero_le' (hϖ ▸ uniformizer_lt_one) (by omega)
  have key : ∀ X Z : Matrix A D k, IsPrimFrame (latA ϖ e (diagLat c)) X →
      Z ∈ matLat A (ϖ ^ e • latA ϖ e (diagLat c)) → ∃ κ ∈ glLatCong (ϖ ^ e) (latA ϖ e (diagLat c)),
        X + Z = X * κ.val := by
    rw [latA, dualLat_diagLat, smul_diagLat]
    exact GlobalTheory.PrimFrameMove.exists_glLatCong_move k A D _ _ hlt
  have prim : ∀ X Z : Matrix A D k, IsPrimFrame (latA ϖ e (diagLat c)) X →
      Z ∈ matLat A (ϖ ^ e • latA ϖ e (diagLat c)) → IsPrimFrame (latA ϖ e (diagLat c)) (X + Z) := by
    intro X Z hX hZ
    obtain ⟨κ, hκ, h⟩ := key X Z hX hZ
    rw [h]
    exact GlobalTheory.SplitFlip.Model.isPrimFrame_mul hX κ hκ.1
  refine ⟨fun X hX => if_neg fun h => hX h.2.1, fun X Z hZ => ?_⟩
  by_cases hX : IsPrimFrame (latA ϖ e (diagLat c)) X
  · unfold phiA
    rw [if_pos hX, if_pos (prim X Z hX hZ)]
    obtain ⟨κ, hκ, h⟩ := key X Z hX hZ
    obtain ⟨h1, h2⟩ := invT_mem_of_dual (mem_glLatCong_of_smul hκ)
    obtain ⟨g, rfl⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).1 hX.1
    have h3 : X0 k σ * (invT g).val * κ.val = X0 k σ * (invT (g * invT κ)).val := by
      rw [map_mul, invT_invT, Units.val_mul, Matrix.mul_assoc]
    have hf := @splitTheta_fFun_frameFirstBlock_mul k _ _ _ _ A A' D _ _ _ _ _ _ _ _ μ hμ σ ν Ψ
    rw [h, h3, hf, hf, gdet_mul, map_mul, apow_mul, hν _ h2, apow_of_valuation_eq_one h2.1,
      mul_one, mul_one]
    congr 1
    simp only [smallF, Units.val_mul, ← Matrix.mul_assoc, HasDepth.mul_glLatCong hΨ h1]
  · have hX' : ¬ IsPrimFrame (latA ϖ e (diagLat c)) (X + Z) := fun h => hX (by
      simpa using prim _ (-Z) h (neg_mem hZ))
    unfold phiA
    rw [if_neg hX, if_neg hX']

end GlobalTheory.FrameDepth
end
end
