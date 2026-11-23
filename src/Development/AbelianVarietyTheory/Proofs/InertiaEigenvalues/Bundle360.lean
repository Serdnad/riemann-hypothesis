module

public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle251
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle336
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle337
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle313
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RingTheory.DedekindDomain.Factorization
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

noncomputable section

namespace GlobalTheory.PotExt

variable {l : ℕ} [Fact l.Prime]

section Bridge

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem exists_finExt_of_open (U : Subgroup (Ω ≃ₐ[E] Ω)) (hU : IsOpen (U : Set (Ω ≃ₐ[E] Ω))) :
    ∃ L : FinExt l, ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ GK L → ((Bw.e.symm g : Gw) : Ω ≃ₐ[E] Ω) ∈ U := by
  have hc : Continuous fun g : ↥(GK Bw.Kw) => ((Bw.e.symm g : Gw) : Ω ≃ₐ[E] Ω) :=
    continuous_subtype_val.comp Bw.e_symm_cont
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.1 (hU.preimage hc)
  have h1 : (1 : GQ l) ∈ t := by
    have : (1 : ↥(GK Bw.Kw)) ∈ Subtype.val ⁻¹' t := by
      rw [hts]
      simp [U.one_mem]
    exact this
  obtain ⟨L, hL, hLt⟩ := (krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) t).1 (ht.mem_nhds h1)
  refine ⟨⟨L, hL⟩, fun g hg => ?_⟩
  have : g ∈ Subtype.val ⁻¹' t := hLt hg
  rw [hts] at this
  exact this

theorem rep_apply {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O) (g : ↥(GK Bw.Kw))
    (x : Fin m → ↥Bw.LL.1) :
    Bw.rep r g x = (((r (Bw.e.symm g) : Matrix.GeneralLinearGroup (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x := rfl

end Bridge

end GlobalTheory.PotExt

namespace GlobalTheory.PotExt

variable {l : ℕ} [Fact l.Prime]

section Lat

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem toLL_mem (a : O) : Bw.toLL a ∈ OL Bw.LL := (Bw.eO a).2

theorem mem_stdG_OL {LL : FinExt l} {k : ℕ} (x : Fin k → ↥LL.1) :
    x ∈ stdG ↥(OL LL) ↥LL.1 k ↔ ∀ j, x j ∈ OL LL := by
  constructor
  · rintro ⟨u, rfl⟩ j
    exact (u j).2
  · intro h
    exact ⟨fun j => ⟨x j, h j⟩, rfl⟩


set_option synthInstance.maxHeartbeats 400000 in
def bridgeLat {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O)
    (hr : Continuous fun g => ((r g : Matrix.GeneralLinearGroup (Fin m) O) : Matrix (Fin m) (Fin m) O))
    {K : FinExt l} (h : Bw.Kw.1 ≤ K.1) : LocLat ↥(GK K) ℚ_[l] ↥Bw.LL.1 ↥(OL Bw.LL) where
  V := Fin m → ↥Bw.LL.1
  ρ := (Bw.rep r).comp (Subgroup.inclusion (GK_le h))
  cont := fun x => by
    have h1 : Continuous fun g : ↥(GK K) =>
        ((r (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) : Matrix.GeneralLinearGroup (Fin m) O) :
          Matrix (Fin m) (Fin m) O) :=
      hr.comp (Bw.e_symm_cont.comp (continuous_subtype_val.subtype_mk _))
    have h2 : Continuous (Bw.toLL) := continuous_subtype_val.comp Bw.eO_cont
    exact (h1.matrix_map h2).matrix_mulVec continuous_const
  L :=
    { T := stdG ↥(OL Bw.LL) ↥Bw.LL.1 m
      stable := fun g x hx => by
        rw [mem_stdG_OL] at hx ⊢
        intro j
        simp only [MonoidHom.comp_apply, GlobalTheory.PotExt.rep_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
        exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (toLL_mem Bw _) (hx b)
      fg := by
        rw [stdG, LinearMap.range_eq_map]
        exact (Module.Finite.fg_top).map _
      free := Module.Free.of_equiv (LinearEquiv.ofInjective _ (stdG_inj Subtype.val_injective m))
      span := by
        rw [eq_top_iff, ← (Pi.basisFun ↥Bw.LL.1 (Fin m)).span_eq]
        apply Submodule.span_mono
        rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_⟩
        funext j'
        simp [Pi.single_apply] }

theorem isCrys_up (LT : LocTheory) (hres : ElementDenominator.CrystallineRestrictionToExtension LT) {m : ℕ}
    (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O)
    (hr : Continuous fun g => ((r g : Matrix.GeneralLinearGroup (Fin m) O) : Matrix (Fin m) (Fin m) O))
    {K₁ K₂ : FinExt l} (h₁ : Bw.Kw.1 ≤ K₁.1) (h₁₂ : K₁.1 ≤ K₂.1)
    (hc : IsCrys ((LT l).PD K₁) ((Bw.rep r).comp (Subgroup.inclusion (GK_le h₁)))) :
    IsCrys ((LT l).PD K₂) ((Bw.rep r).comp (Subgroup.inclusion (GK_le (h₁.trans h₁₂)))) :=
  (hres l K₂ K₁ h₁₂ (GK_le h₁₂) Bw.LL (bridgeLat Bw r hr h₁) hc).1

end Lat

end GlobalTheory.PotExt

namespace GlobalTheory.PotExt

variable {l : ℕ} [Fact l.Prime]

theorem Kur_stable (σ : GQ l) {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : σ x ∈ MaximalUnramifiedExtension l := by
  have h : (MaximalUnramifiedExtension l).map (σ : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, ⟨m, hm, hlm, hy⟩, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, by rw [← map_pow, hy, map_one]⟩
  exact h ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)

theorem mem_of_normal {K' : FinExt l} (hn : Normal ℚ_[l] K'.1) (σ : GQ l) {x : Om l} (hx : x ∈ K'.1) :
    σ x ∈ K'.1 :=
  IntermediateField.normal_iff_forall_map_le'.1 hn σ ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)

theorem GKin_normal {K K' : FinExt l} (h : K.1 ≤ K'.1) (hn : Normal ℚ_[l] K'.1) : (GKin h).Normal := by
  haveI : IsGalois ℚ_[l] K'.1 := IsGalois.mk
  haveI : (GK K').Normal := (InfiniteGalois.normal_iff_isGalois K'.1).2 inferInstance
  unfold GKin
  infer_instance

theorem GKin_finiteIndex {K K' : FinExt l} (h : K.1 ≤ K'.1) : (GKin h).FiniteIndex := by
  haveI : Finite (GQ l ⧸ GK K') := Subgroup.quotient_finite_of_isOpen _ (@IntermediateField.fixingSubgroup_isOpen _ _ _ _ _ K'.1 K'.2)
  haveI : (GK K').FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  unfold GKin
  infer_instance

theorem maxUnramifiedSubfield_stable_of_normal (P : LocPrime l) {K K' : FinExt l} (hn : Normal ℚ_[l] K'.1) (g : ↥(GK K)) (c : ↥(K0 K')) :
    ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c' := by
  have hc1 : ((c : Om l)) ∈ K'.1 := c.2.1
  have hc2 : ((c : Om l)) ∈ MaximalUnramifiedExtension l := c.2.2
  refine ⟨⟨(g : GQ l) c, mem_of_normal hn _ hc1, Kur_stable _ hc2⟩, ?_⟩
  rw [P.PD_actB]
  exact P.actQ_Kur (g : GQ l) ⟨c, hc2⟩ ⟨(g : GQ l) c, Kur_stable _ hc2⟩ rfl

end GlobalTheory.PotExt

namespace GlobalTheory.PotExt

theorem main : ∀ (D : D7) (P : Pend D), ElementDenominator.adm12 D → ∀ (i : D.nd.Loc) (k : Fin 2)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (Y : Finset (Fb (D.host.g k) (D.host.g_prime k))), (∀ y ∈ Y, y ≠ 0) →
  ∀ (ι : Type) [Finite ι] (n : ℕ) (R : ι → (GE D.nd →* GL (Fin n) (D.nd.O i))) (n₀ : ℕ)
    (R₀ : GE D.nd →* GL (Fin n₀) (D.nd.O i)),
  (∀ j, Continuous fun g => ((R j g : GL (Fin n) (D.nd.O i)) : Matrix (Fin n) (Fin n) (D.nd.O i))) →
  (Continuous fun g => ((R₀ g : GL (Fin n₀) (D.nd.O i)) : Matrix (Fin n₀) (Fin n₀) (D.nd.O i))) →
  (∀ j, Br.IsPotCrysW D.loc D.nbr i w hw (R j)) → Br.IsPotCrysW D.loc D.nbr i w hw R₀ →
  ∃ (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
      (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
        ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
          algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c'),
    (∀ j, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((R j).comp (decS D.nd w)))) ∧
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (R₀.comp (decS D.nd w))) ∧
    ∀ y ∈ Y, ∀ g ∈ GKin h,
      (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
        P.om k w y (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) = 1 := by
  intro D P hadm i k w hw Y hY ι _ n R n₀ R₀ hRc hR₀c hRp hR₀p
  unfold Br.IsPotCrysW LocBridge.IsPotCrysW at hRp hR₀p
  choose Kj hj hcj using hRp
  obtain ⟨K₀', h₀, hc₀⟩ := hR₀p
  have hLy : ∀ y : ↥Y, ∃ L : FinExt (D.nd.l i), ∀ g : ↥(GK (D.nbr i w hw).Kw), (g : GQ (D.nd.l i)) ∈ GK L →
      (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
      P.om k w y (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) = 1 := by
    intro y
    obtain ⟨U, hU, hUo⟩ := P.om_open k w y (hY y y.2)
    obtain ⟨L, hL⟩ := exists_finExt_of_open (D.nbr i w hw) U hU
    exact ⟨L, fun g hg hI => hUo _ (hL g hg) hI⟩
  choose Ly hLy using hLy
  haveI : ∀ j, FiniteDimensional ℚ_[D.nd.l i] (Kj j).1 := fun j => (Kj j).2
  haveI : ∀ y, FiniteDimensional ℚ_[D.nd.l i] (Ly y).1 := fun y => (Ly y).2
  haveI := (D.nbr i w hw).Kw.2
  haveI := K₀'.2
  let M : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)) :=
    (D.nbr i w hw).Kw.1 ⊔ K₀'.1 ⊔ (⨆ j, (Kj j).1) ⊔ (⨆ y, (Ly y).1)
  haveI : FiniteDimensional ℚ_[D.nd.l i] M := by infer_instance
  let K' : FinExt (D.nd.l i) := ⟨IntermediateField.normalClosure ℚ_[D.nd.l i] M (Om (D.nd.l i)), inferInstance⟩
  have hMK : M ≤ K'.1 := IntermediateField.le_normalClosure M
  have hn : Normal ℚ_[D.nd.l i] K'.1 := normalClosure.normal _ _ _
  have h : (D.nbr i w hw).Kw.1 ≤ K'.1 := le_trans (le_sup_left.trans (le_sup_left.trans le_sup_left)) hMK
  have h0K : K₀'.1 ≤ K'.1 := le_trans (le_sup_right.trans (le_sup_left.trans le_sup_left)) hMK
  refine ⟨K', h, GKin_normal h hn, GKin_finiteIndex h, maxUnramifiedSubfield_stable_of_normal _ hn, fun j => ?_, ?_, ?_⟩
  · have hjK : (Kj j).1 ≤ K'.1 :=
      le_trans ((le_iSup (fun j => (Kj j).1) j).trans (le_sup_right.trans le_sup_left)) hMK
    refine (GlobalTheory.PcRes.main _ _ _ _ _ h _ _ _ _ _).2.2 ?_
    exact isCrys_up (D.nbr i w hw) D.loc hadm _ ((hRc j).comp continuous_subtype_val) (hj j) hjK (hcj j)
  · refine (GlobalTheory.PcRes.main _ _ _ _ _ h _ _ _ _ _).2.2 ?_
    exact isCrys_up (D.nbr i w hw) D.loc hadm _ (hR₀c.comp continuous_subtype_val) h₀ h0K hc₀
  · intro y hy g hg hI
    have hyK : (Ly ⟨y, hy⟩).1 ≤ K'.1 :=
      le_trans ((le_iSup (fun y => (Ly y).1) ⟨y, hy⟩).trans le_sup_right) hMK
    exact hLy ⟨y, hy⟩ g (GK_le hyK (Subgroup.mem_subgroupOf.1 hg)) hI

end GlobalTheory.PotExt
end
end

section

open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.UnitDiscAlg.Red

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

def Sm (s : Matrix (Fin n) (Fin n) E) : Prop := ∀ i j, ‖s i j‖ < 1

theorem sm_add {x y : Matrix (Fin n) (Fin n) E} (hx : Sm x) (hy : Sm y) : Sm (x + y) := by
  intro i j
  rw [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hx i j) (hy i j))

theorem sm_neg {x : Matrix (Fin n) (Fin n) E} (hx : Sm x) : Sm (-x) := by
  intro i j; rw [Matrix.neg_apply, norm_neg]; exact hx i j

theorem sm_zero : Sm (0 : Matrix (Fin n) (Fin n) E) := by intro i j; simp

theorem norm_sum_lt_one' {s : Finset (Fin n)} {f : Fin n → E} (h : ∀ k, ‖f k‖ < 1) :
    ‖∑ k ∈ s, f k‖ < 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (h a) ih)

theorem sm_mul_left {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : Sm y) :
    Sm (x * y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact norm_sum_lt_one' (fun k => by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hx i k)) (hy k j))

theorem sm_mul_right {x y : Matrix (Fin n) (Fin n) E} (hx : Sm x) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    Sm (x * y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact norm_sum_lt_one' (fun k => by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hy k j)) (hx i k))

theorem sm_eq_smul {N s : Matrix (Fin n) (Fin n) E} {ϖ : E} (h0 : 0 < ‖ϖ‖)
    (hu : ∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) (hs : Sm s) (hc : s * N = N * s) :
    ∃ a : Matrix (Fin n) (Fin n) E, a * N = N * a ∧ (∀ i j, ‖a i j‖ ≤ 1) ∧ s = ϖ • a := by
  have hϖ : ϖ ≠ 0 := norm_pos_iff.mp h0
  refine ⟨ϖ⁻¹ • s, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, hc]
  · intro i j
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ h0, mul_one]
    exact hu _ (hs i j)
  · rw [smul_smul, mul_inv_cancel₀ hϖ, one_smul]

end GlobalTheory.UnitDiscAlg.Red

namespace GlobalTheory.UnitDiscAlg.Red
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

theorem exists_pow_close [LocallyCompactSpace E] (y : Matrix (Fin n) (Fin n) E)
    (hy : ∀ i j, ‖y i j‖ ≤ 1) : ∃ a b : ℕ, a < b ∧ Sm (y ^ b - y ^ a) := by
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  let f : ℕ → Fin n → Fin n → E := fun k i j => (y ^ k) i j
  have hs : IsCompact (Metric.closedBall (0 : Fin n → Fin n → E) 1) := isCompact_closedBall _ _
  have hf : ∀ k, f k ∈ Metric.closedBall (0 : Fin n → Fin n → E) 1 := by
    intro k
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    exact integ_pow hy k i j
  obtain ⟨x, -, φ, hφ, hlim⟩ := hs.tendsto_subseq hf
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq 1 one_pos
  refine ⟨φ N, φ (N + 1), hφ (Nat.lt_succ_self N), ?_⟩
  intro i j
  have h1 := hN (N + 1) (Nat.le_succ N) N le_rfl
  have h2 : dist (f (φ (N + 1)) i j) (f (φ N) i j) < 1 :=
    lt_of_le_of_lt ((dist_le_pi_dist _ _ j).trans (dist_le_pi_dist _ _ i)) h1
  rw [dist_eq_norm] at h2
  simpa [f, Matrix.sub_apply] using h2

end GlobalTheory.UnitDiscAlg.Red

namespace GlobalTheory.UnitDiscAlg.Red

theorem main : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [LocallyCompactSpace E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (ϖ : E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) → ∀ y : Matrix (Fin n) (Fin n) E, y * N = N * y → (∀ i j, ‖y i j‖ ≤ 1) → ∃ x z a₁ a₂ a₃ : Matrix (Fin n) (Fin n) E, (x * N = N * x ∧ z * N = N * z ∧ a₁ * N = N * a₁ ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) ∧ (∀ i j, ‖x i j‖ ≤ 1 ∧ ‖z i j‖ ≤ 1 ∧ ‖a₁ i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) ∧ x * x - x = ϖ • a₁ ∧ y * (1 - x) = ϖ • a₂ ∧ y * z * x - x = ϖ • a₃ := by
  intro E _ _ _ n N ϖ hN hB h0 _ hu y hyN hy
  have hred := GlobalTheory.T.commuting_integral_matrix_topnil E n N hN hB
  obtain ⟨a, b, hab, hsm⟩ := exists_pow_close y hy
  have hcy : Commute y N := hyN
  have step : ∀ k, a ≤ k → Sm (y ^ (k + (b - a)) - y ^ k) := by
    intro k hk
    have e1 : y ^ (k + (b - a)) - y ^ k = y ^ (k - a) * (y ^ b - y ^ a) := by
      rw [mul_sub, ← pow_add, ← pow_add]
      congr 2 <;> omega
    rw [e1]
    exact sm_mul_left (integ_pow hy _) hsm
  have per : ∀ k, a ≤ k → ∀ j, Sm (y ^ (k + j * (b - a)) - y ^ k) := by
    intro k hk j
    induction j with
    | zero => simpa using (sm_zero : Sm (0 : Matrix (Fin n) (Fin n) E))
    | succ j ih =>
      have e2 : y ^ (k + (j + 1) * (b - a)) - y ^ k
          = (y ^ (k + j * (b - a) + (b - a)) - y ^ (k + j * (b - a)))
            + (y ^ (k + j * (b - a)) - y ^ k) := by
        rw [show k + (j + 1) * (b - a) = k + j * (b - a) + (b - a) by ring]
        abel
      rw [e2]
      exact sm_add (step _ (by omega)) ih
  set M := (b - a) * (a + 1) with hMdef
  have hpos : 1 ≤ b - a := by omega
  have hMa : a + 1 ≤ M := by
    rw [hMdef]; nlinarith
  have hidem : Sm (y ^ M * y ^ M - y ^ M) := by
    rw [← pow_add]
    have := per M (by omega) (a + 1)
    rwa [show M + (a + 1) * (b - a) = M + M by rw [hMdef]; ring] at this
  set x := y ^ M with hx
  have hxi : ∀ i j, ‖x i j‖ ≤ 1 := integ_pow hy M
  have hxN : Commute x N := hcy.pow_left M
  have hyx : Commute y x := (Commute.refl y).pow_right M
  have h1i : ∀ i j, ‖((1 : Matrix (Fin n) (Fin n) E) - x) i j‖ ≤ 1 := integ_sub integ_one hxi

  have hwM : Sm ((y * (1 - x)) ^ M) := by
    have hc : Commute y (1 - x) := (Commute.one_right y).sub_right hyx
    rw [hc.mul_pow, ← hx]
    obtain ⟨m, hm⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    rw [hm, pow_succ', ← mul_assoc]
    apply sm_mul_right _ (integ_pow h1i m)
    have : x * (1 - x) = -(x * x - x) := by rw [mul_sub, mul_one]; abel
    rw [this]
    exact sm_neg hidem
  have hwN : Commute (y * (1 - x)) N := hcy.mul_left ((Commute.one_left N).sub_left hxN)
  have hw : Sm (y * (1 - x)) :=
    hred (y * (1 - x)) hwN.eq (integ_mul hy h1i) M hwM
  have hc1 : Commute (x * x - x) N := (hxN.mul_left hxN).sub_left hxN
  obtain ⟨a₁, ha₁N, ha₁i, ha₁⟩ := sm_eq_smul h0 hu hidem hc1.eq
  obtain ⟨a₂, ha₂N, ha₂i, ha₂⟩ := sm_eq_smul h0 hu hw hwN.eq
  have hyz : y * y ^ (M - 1) = x := by
    rw [hx, ← pow_succ']; congr 1; omega
  refine ⟨x, y ^ (M - 1), a₁, a₂, a₁, ⟨hxN.eq, (hcy.pow_left _).eq, ha₁N, ha₂N, ha₁N⟩,
    fun i j => ⟨hxi i j, integ_pow hy _ i j, ha₁i i j, ha₂i i j, ha₁i i j⟩, ha₁, ha₂, ?_⟩
  rw [hyz, ha₁]

end GlobalTheory.UnitDiscAlg.Red
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

theorem _root_.GlobalTheory.T.minpoly_separable_of_complex_normal_reading : ∀ (K V H : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (φ : K →+* ℂ) (j : V →ₛₗ[φ] H) (T : Module.End K V) (S S' : Module.End ℂ H), (∀ (n : ℕ) (x : Fin n → V), LinearIndependent K x → LinearIndependent ℂ (fun a => j (x a))) → (∀ x, j (T x) = S (j x)) → (∀ u ∈ Submodule.span ℂ (Set.range j), S' u ∈ Submodule.span ℂ (Set.range j)) → (∀ u ∈ Submodule.span ℂ (Set.range j), ∀ v ∈ Submodule.span ℂ (Set.range j), inner ℂ (S u) v = inner ℂ u (S' v)) → (∀ u ∈ Submodule.span ℂ (Set.range j), S (S' u) = S' (S u)) → (minpoly K T).Separable := by
  first | exact @GlobalTheory.NormalSeparable.minpoly_separable_of_normal | exact GlobalTheory.NormalSeparable.minpoly_separable_of_normal | (intros; apply GlobalTheory.NormalSeparable.minpoly_separable_of_normal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

theorem _root_.GlobalTheory.T.split_charpoly_lattice_kills_span : ∀ (O V B : Type) [CommRing O] [IsDomain O] [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V] [AddCommGroup B] [Module O B] [Module.Free O B] [Module.Finite O B] (e : B →ₗ[O] V) (t : Module.End O B) (T : Module.End (FractionRing O) V), (∀ x, e (t x) = T (e x)) → ((LinearMap.charpoly t).map (algebraMap O (FractionRing O))).Splits → ∃ p : (FractionRing O)[X], p ≠ 0 ∧ p.Splits ∧ ∀ x ∈ Submodule.span (FractionRing O) (Set.range e), Polynomial.aeval T p x = 0 := by
  first | exact @GlobalTheory.charpoly_split_kills_span | exact GlobalTheory.charpoly_split_kills_span | (intros; apply GlobalTheory.charpoly_split_kills_span <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf

noncomputable section

namespace GlobalTheory.TripleLocal

theorem frobConj_natCast_notMem (E : Type) [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime] :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  have h0 : (Ideal.span {((l : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hl.out.ne_zero
  rw [Filter.eventually_cofinite]
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simpa [Ideal.dvd_span_singleton] using hw

end GlobalTheory.TripleLocal

end
end
