module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.PeriodIntegrals.Bundle006
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle003
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle007
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle200
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DiscriminantKernelAutomorphisms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.GapAtRealPlaces

theorem gapBig_of_comparison (h : PI.ScGapBig.ScGapBig) (D : Formalism.BasicNotions.D7) :
    Formalism.L2.SG.SplitPrimeNormLemmas.GapBigOfGapHyp D := by
  intro hm hG τ

  have hr : PI.ScGapBig.rk48 D.R.k D.R.rS = D.R.r := by
    simp only [PI.ScGapBig.rk48, Formalism.BasicNotions.Ranks.r]
    omega

  have hgaps : ∀ (j : Fin (2 * D.R.rS + 2)) (hj : j.val + 1 < 2 * D.R.rS + 2),
      16 * (PI.ScGapBig.rk48 D.R.k D.R.rS : ℝ) ^ 19 ≤
        ((D.hc τ).b (Fin.cast hm.symm ⟨j.val + 1, hj⟩) : ℝ) - ((D.hc τ).b (Fin.cast hm.symm j) : ℝ) := by
    intro j hj
    have hlt : (Fin.cast hm.symm j).val + 1 < D.R.m := by
      rw [Fin.val_cast]
      omega
    have key := hG.2 τ (Fin.cast hm.symm j) hlt
    have hidx : (⟨(Fin.cast hm.symm j).val + 1, hlt⟩ : Fin D.R.m) = Fin.cast hm.symm ⟨j.val + 1, hj⟩ :=
      Fin.ext rfl
    rw [hidx] at key
    rw [hr]
    exact_mod_cast key
  obtain ⟨t, hto, ht5, ht1801, hgap⟩ :=
    h D.R.k D.R.rS (fun j => ((D.hc τ).b (Fin.cast hm.symm j) : ℝ)) (hr ▸ hG.1) hgaps
  exact ⟨t, hto, ht5, ht1801, hgap⟩

theorem gapBigOfGapHyp : ∀ D : D7, GapBigOfGapHyp D := by
  intro D
  exact gapBig_of_comparison scGapBig D

end GlobalTheory.GapAtRealPlaces
end

section

noncomputable section

open scoped Classical

namespace GlobalTheory.RowMassCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pieces

variable (D : D7) (u : D.what₂.Word)

end Pieces

section Gmap

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem gmap_mul' (a b : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

theorem gmap_one' (M : Submodule (𝓞 K) V) : Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) M = M := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

end Gmap

section Stab

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem mul_mem_stabF {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ha : a ∈ stabF D F0) (hb : b ∈ stabF D F0) :
    a * b ∈ stabF D F0 := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ha.1 hb.1, fun j => ?_, ?_⟩
  · have : ((a * b : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) =
        (a : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ (b : (VS D).V →ₗ[D.host.E] (VS D).V) := rfl
    rw [this, Submodule.map_comp, hb.2.1 j, ha.2.1 j]
  · show a (b F0.z) = F0.z
    rw [hb.2.2, ha.2.2]

end Stab

end GlobalTheory.RowMassCompare

end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isClosedEmbedding_of_congruenceSubgroups_conj : ∀ (I I' : AutInst) (j : I'.Gf →* I.Gf) (xf : I.Gf), (∀ (N : ℕ) (g : I'.Gf), g ∈ I'.Kg N ↔ xf⁻¹ * j g * xf ∈ I.Kg N) → Topology.IsClosedEmbedding j := by
  first | exact @GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg | exact GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg | (intros; apply GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.AdelicLatticeSwap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))

private lemma mem_intAf_of_mem_intAd {a : Af F} (ha : a ∈ Formalism.UG.intAd F) : a ∈ Formalism.MainNotions.StandardLattice.intAf F := by
  intro v
  exact ha v

private lemma mem_intAd_of_mem_intAf {a : Af F} (ha : a ∈ Formalism.MainNotions.StandardLattice.intAf F) : a ∈ Formalism.UG.intAd F := by
  intro v
  exact ha v

private lemma intAf_mul_mem {a b : Af F} (ha : a ∈ Formalism.MainNotions.StandardLattice.intAf F) (hb : b ∈ Formalism.MainNotions.StandardLattice.intAf F) :
    a * b ∈ Formalism.MainNotions.StandardLattice.intAf F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)

private lemma one_mem_intAf_flag_measures : (1 : Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := by
  intro v
  rw [map_one]
  exact one_mem _


omit [NumberField E] in
theorem gen_smul_mem (a : Af F) (ha : a ∈ Formalism.UG.intAd F) (c : 𝓞 E)
    (y : Fin n → Af F ⊗[F] E) (hy : y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))) :
    (a ⊗ₜ[F] (c : E) : Af F ⊗[F] E) • y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  unfold Formalism.MainNotions.StandardLattice.latHat at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hw
    apply AddSubgroup.subset_closure
    refine ⟨a * b, intAf_mul_mem (mem_intAf_of_mem_intAd ha) hb, c • x, L.smul_mem c hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
  | neg u _ hu => rw [smul_neg]; exact neg_mem hu

theorem int_smul_mem (t : E ⊗[F] Af F) (ht : t ∈ Formalism.MainNotions.S.IntAf F E) :
    ∀ y : Fin n → Af F ⊗[F] E, y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) →
      (Algebra.TensorProduct.comm F (Af F) E).symm t • y ∈
        Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt at ht
  induction ht using Subring.closure_induction with
  | mem s hs =>
    intro y hy
    rcases hs with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
    · obtain ⟨c, rfl⟩ := he
      rw [Algebra.TensorProduct.comm_symm_tmul]
      exact gen_smul_mem L 1 (one_mem _) c y hy
    · rw [Algebra.TensorProduct.comm_symm_tmul]
      simpa using gen_smul_mem L b hb 1 y hy
  | zero => intro y _; rw [map_zero, zero_smul]; exact zero_mem _
  | one => intro y hy; rw [map_one, one_smul]; exact hy
  | add s u _ _ hs hu => intro y hy; rw [map_add (f := _), add_smul]; exact add_mem (hs y hy) (hu y hy)
  | neg s _ hs => intro y hy; rw [map_neg, neg_smul]; exact neg_mem (hs y hy)
  | mul s u _ _ hs hu => intro y hy; rw [map_mul, mul_smul]; exact hs _ (hu y hy)

theorem symm_mem_of_mem (z : Fin n → E ⊗[F] Af F) (hz : z ∈ Formalism.MainNotions.S.lamAf (F := F) L) :
    (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (z i)) ∈
      Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  unfold Formalism.MainNotions.S.lamAf at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨x, hx⟩, rfl⟩ := hw
    unfold Formalism.MainNotions.StandardLattice.latHat
    apply AddSubgroup.subset_closure
    refine ⟨1, one_mem_intAf_flag_measures, x, hx, ?_⟩
    funext i
    show (Algebra.TensorProduct.comm F (Af F) E).symm ((x i) ⊗ₜ[F] (1 : Af F)) = (1 : Af F) ⊗ₜ[F] x i
    simp
  | zero =>
    have h0 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((0 : Fin n → E ⊗[F] Af F) i)) = 0 := by
      funext i
      simp
    rw [h0]
    exact zero_mem _
  | add u w _ _ hu hw =>
    have h1 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((u + w) i)) =
        (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (u i)) +
          fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (w i) := by
      funext i
      simp
    rw [h1]
    exact add_mem hu hw
  | smul s u _ hu =>
    have h2 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((s • u) i)) =
        (Algebra.TensorProduct.comm F (Af F) E).symm (s : E ⊗[F] Af F) •
          fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (u i) := by
      funext i
      simp [Subring.smul_def]
    rw [h2]
    exact int_smul_mem L s s.2 _ hu

theorem mem_latHat_iff_comm_mem_lamAf (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (y : Fin n → Af F ⊗[F] E) :
    y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔
      (fun i => Algebra.TensorProduct.comm F (Af F) E (y i)) ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  constructor
  · intro hy
    unfold Formalism.MainNotions.StandardLattice.latHat at hy
    induction hy using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hw
      have hg : (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ Formalism.MainNotions.S.lamAf (F := F) L :=
        Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      have hs : ((1 : E) ⊗ₜ[F] a : E ⊗[F] Af F) ∈ Formalism.MainNotions.S.IntAf F E :=
        Subring.subset_closure (Or.inr ⟨⟨a, mem_intAd_of_mem_intAf ha⟩, rfl⟩)
      convert Submodule.smul_mem _ (⟨_, hs⟩ : Formalism.MainNotions.S.IntAf F E) hg using 1
      funext i
      simp [Subring.smul_def, Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul]
    | zero =>
      convert zero_mem (Formalism.MainNotions.S.lamAf (F := F) L) using 1
      funext i
      simp
    | add u w _ _ hu hw =>
      convert add_mem hu hw using 1
      funext i
      simp
    | neg u _ hu =>
      convert neg_mem hu using 1
      funext i
      simp
  · intro hz
    simpa using symm_mem_of_mem L _ hz

end GlobalTheory.AdelicLatticeSwap
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdmFlagSub

open IsDedekindDomain Formalism.HermitianLatticesTheory

section Loc

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [hp : p.IsPrime]

theorem mem_localization_iff (L : Submodule R W) (x : W) :
    x ∈ localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := Iff.rfl

theorem le_localized_self (L : Submodule R W) : L ≤ localization₂ p L := fun x hx =>
  (mem_localization_iff p L x).2 ⟨1, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hx⟩

theorem localization_le_of_le_localization₂ {L N : Submodule R W} (h : L ≤ localization₂ p N) : localization₂ p L ≤ localization₂ p N := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := (mem_localization_iff p L x).1 hx
  obtain ⟨t, ht, htx⟩ := (mem_localization_iff p N _).1 (h hsx)
  refine (mem_localization_iff p N x).2 ⟨t * s, fun hm => ?_, by rwa [mul_smul]⟩
  rcases hp.mem_or_mem hm with h1 | h1
  · exact ht h1
  · exact hs h1

end Loc

theorem mem_of_forall_locP {E W : Type} [Field E] [NumberField E] [AddCommGroup W]
    [Module (𝓞 E) W] (N : Submodule (𝓞 E) W) (x : W)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), x ∈ (haveI := P.isPrime; localization₂ P.asIdeal N)) : x ∈ N := by
  by_contra hx
  let I : Ideal (𝓞 E) := N.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
  have hI : I ≠ ⊤ := by
    intro hI
    have : (1 : 𝓞 E) ∈ I := by rw [hI]; trivial
    apply hx
    simpa [I] using this
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
  obtain ⟨s, hs, hsx⟩ := h ⟨M, hM.isPrime, hM0⟩
  exact hs (hIM (by simpa [I] using hsx))

theorem xLam_le_smul_sup_xLam :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
      (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T'),
      IsFixedConv Λ g F → IsFixedConv Λ g F' → IsAdmissible Λ g F F' →
        XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F' := by
  intro E _ _ _ S r T T' Λ g F F' hF hF' hA x hx
  obtain ⟨ξ, hξ0, hξ1, hξ⟩ := hA
  set N : Submodule (𝓞 E) S.V := Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F' with hN
  apply mem_of_forall_locP
  intro P
  haveI := P.isPrime
  by_cases hg : (g : 𝓞 E) ∈ P.asIdeal
  swap
  · refine (mem_localization_iff _ _ _).2 ⟨g, hg, Submodule.mem_sup_left ?_⟩
    exact Submodule.smul_mem_smul (Ideal.subset_span rfl) hx.1
  obtain ⟨c, -, hc1, hc⟩ := hF.1 P
  obtain ⟨c', -, hc1', hc'⟩ := hF'.1 P
  simp only [hc1 hg, one_smul] at hc
  simp only [hc1' hg, one_smul] at hc'
  have he' : ∀ b, F'.fl.e b ∈ localization₂ P.asIdeal N := by
    intro b
    have h1 : F'.fl.e b ∈ localization₂ P.asIdeal (XLam Λ F') := by
      rw [hc']
      exact le_localized_self _ _ (Submodule.subset_span ⟨b, rfl⟩)
    exact localization_le_of_le_localization₂ _ (le_sup_right.trans (le_localized_self _ _)) h1
  have hf : ∀ n : ℕ, ∀ b : Fin r, b.1 = n → F.fl.e b ∈ localization₂ P.asIdeal N := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro b hb
      have h1 : frame F' b.castSucc - frameAct (frame F) ξ b.castSucc ∈ localization₂ P.asIdeal N :=
        localization_le_of_le_localization₂ _ (le_sup_left.trans (le_localized_self _ _)) (hξ b.castSucc P hg)
      have h2 : frame F' b.castSucc = F'.fl.e b := by simp [frame, FlagG.fvec]
      have h3 : frameAct (frame F) ξ b.castSucc ∈ localization₂ P.asIdeal N := by
        have := Submodule.sub_mem _ (he' b) h1
        rw [h2] at this
        simpa using this
      have h4 : frameAct (frame F) ξ b.castSucc =
          F.fl.e b + ∑ a ∈ Finset.univ.erase b, ξ a.castSucc b.castSucc • F.fl.e a := by
        unfold frameAct
        rw [Fin.sum_univ_castSucc, hξ0 (Fin.last r) b.castSucc (Fin.castSucc_lt_last b),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ b), hξ1]
        simp only [frame, FlagG.fvec, Fin.snoc_castSucc, RingOfIntegers.coe_eq_algebraMap, map_zero,
          map_one, zero_smul, add_zero, one_smul, algebraMap_smul]
      have h5 : ∑ a ∈ Finset.univ.erase b, ξ a.castSucc b.castSucc • F.fl.e a ∈
          localization₂ P.asIdeal N := by
        refine Submodule.sum_mem _ fun a ha => ?_
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase ha) with hab | hab
        · exact Submodule.smul_mem _ _ (ih a.1 (hb ▸ hab) a rfl)
        · rw [hξ0 _ _ (Fin.castSucc_lt_castSucc_iff.2 hab), zero_smul]
          exact Submodule.zero_mem _
      rw [h4] at h3
      simpa using Submodule.sub_mem _ h3 h5
  have hx' : x ∈ localization₂ P.asIdeal (XLam Λ F) := le_localized_self _ _ hx
  rw [hc] at hx'
  refine localization_le_of_le_localization₂ _ ?_ hx'
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact hf _ a rfl

end GlobalTheory.AdmFlagSub

end
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.LatChain

section
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem mem_orth {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem exists_mul_mem {Λ : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsFullLattice E Λ) (v : S.V) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set S.V) := by
    letI := hΛ
    rw [Submodule.IsFullLattice.span_eq_top]; trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩

theorem le_spanE {Λ M : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsFullLattice E Λ) {U : Submodule E S.V}
    (h : Λ ⊓ toO S U ≤ M) : U ≤ spanE S M := by
  intro v hv
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem hΛ v
  have h0 : d • v ∈ toO S U := (toO S U).smul_mem d hv
  have h1 : d • v ∈ M := h ⟨hd, h0⟩
  have h2 := Submodule.smul_mem _ (algebraMap (𝓞 E) E d)⁻¹ (Submodule.subset_span (R := E) h1)
  rwa [← algebraMap_smul E d v, inv_smul_smul₀
    ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)] at h2

theorem spanE_le {M : Submodule (𝓞 E) S.V} {U : Submodule E S.V} (h : M ≤ toO S U) : spanE S M ≤ U :=
  Submodule.span_le.2 h

variable {r : ℕ} {T T' : E} {Λ : Submodule (𝓞 E) S.V}

theorem mem_L0sub {F : LFlag S r T} {x : S.V} (hx : x ∈ Lrep Λ F) (hz : S.hT F.fl.z x = 0) :
    x ∈ L0sub Λ F :=
  ⟨⟨Submodule.mem_sup_left hx, hx.2⟩, hz⟩

theorem thp_le_la (g : ℕ) {F : LFlag S r T} {F' : LFlag S r T'} (hΛ : Submodule.IsFullLattice E Λ)
    (hF : IsLift Λ F) (hF' : IsLift Λ F') : Thp Λ F F' ≤ La Λ g F F' := by
  intro x hx
  have hperp : ∀ y ∈ UUE Λ F F', S.hT y x = 0 := mem_orth.1 hx.2
  have hX : Xsp F ≤ UUE Λ F F' :=
    le_spanE hΛ (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
  have hX' : Xsp F' ≤ UUE Λ F F' := le_spanE hΛ (le_sup_of_le_left le_sup_right)
  have hz : F.fl.z ∈ UUE Λ F F' := by
    rw [← hF.2]
    exact Submodule.subset_span (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))))
  have hz' : F'.fl.z ∈ UUE Λ F F' := by
    rw [← hF'.2]
    exact Submodule.subset_span (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have h1 : x ∈ Lrep Λ F := ⟨hx.1, mem_orth.2 fun y hy => hperp y (hX hy)⟩
  have h2 : x ∈ Lrep Λ F' := ⟨hx.1, mem_orth.2 fun y hy => hperp y (hX' hy)⟩
  refine Submodule.subset_span ⟨hx.2, mem_L0sub h1 (hperp _ hz), mem_L0sub h2 (hperp _ hz'),
    x, h1, ?_, x, h2, ?_, ?_⟩ <;> rw [sub_self] <;> exact Submodule.zero_mem _

end

theorem lattice_chain_spans : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T'), Submodule.IsFullLattice E Λ → IsLift Λ F → IsLift Λ F' → Thp Λ F F' ≤ La Λ g F F' ∧ La Λ g F F' ≤ L0sub Λ F ⊓ toO S (Hp Λ F F') ∧ spanE S (Thp Λ F F') = Hp Λ F F' ∧ ∀ (F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V), spanE S (Mlat Λ F F' F'' β g) = Th Λ F F' F'' β := by
  intro E _ _ _ S r T T' Λ g F F' hΛ hF hF'
  have h1 := thp_le_la g hΛ hF hF'
  refine ⟨h1, Submodule.span_le.2 fun x hx => ⟨hx.2.1, hx.1⟩,
    le_antisymm (spanE_le inf_le_right) (le_spanE hΛ le_rfl), fun F'' β =>
    le_antisymm (spanE_le inf_le_right) (le_spanE hΛ fun x hx => ⟨h1 ⟨hx.1, ?_⟩, hx.2⟩)⟩
  obtain ⟨p, hp, e⟩ := hx.2
  have : p.1 = x := e
  rw [← this]
  exact hp.1.1.1

end GlobalTheory.LoopC.LatChain
end
