module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle031
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle034
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle035
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UniformizerPowerTorusMemNormalUnitarySubgroup
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LatHecke

open IsLocalRing

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] {r : ℕ}

abbrev Red (N : Submodule O (Fin r → K)) : Type := N ⧸ (maximalIdeal O • ⊤ : Submodule O N)

instance Red.instModule (N : Submodule O (Fin r → K)) : Module (ResidueField O) (Red N) :=
  inferInstanceAs (Module (O ⧸ maximalIdeal O) (Red N))

instance Red.instTower (N : Submodule O (Fin r → K)) : IsScalarTower O (ResidueField O) (Red N) := by
  refine ⟨fun a b x => ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective b
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (a • residue O b) • (Submodule.Quotient.mk x : Red N) = a • (residue O b • (Submodule.Quotient.mk x : Red N))
  have h : ∀ (c : O) (y : N), residue O c • (Submodule.Quotient.mk y : Red N) = Submodule.Quotient.mk (c • y) :=
    fun c y => rfl
  have h2 : a • residue O b = residue O (a * b) := by
    rw [Algebra.smul_def]; simp [ResidueField.algebraMap_eq]
  rw [h2, h, h, mul_smul]; rfl

def pull (N : Submodule O (Fin r → K)) (W : Submodule (ResidueField O) (Red N)) : Submodule O N :=
  (W.restrictScalars O).comap (Submodule.mkQ _)

theorem smul_top_le_pull (N : Submodule O (Fin r → K)) (W : Submodule (ResidueField O) (Red N)) :
    (maximalIdeal O • ⊤ : Submodule O N) ≤ pull N W := by
  intro x hx
  have : Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N) x = 0 := by
    simpa using hx
  simp [pull, this]

theorem card_quot_pull (N : Submodule O (Fin r → K)) (W : Submodule (ResidueField O) (Red N)) :
    Nat.card (N ⧸ pull N W) = Nat.card (Red N ⧸ W) := by
  let f : N →ₗ[O] (Red N ⧸ W) := (W.mkQ.restrictScalars O) ∘ₗ (Submodule.mkQ _)
  have hs : Function.Surjective f :=
    (Submodule.mkQ_surjective W).comp (Submodule.mkQ_surjective _)
  have hk : LinearMap.ker f = pull N W := by
    ext x
    simp [f, pull, LinearMap.mem_ker]
  exact Nat.card_congr
    ((Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hs)).toEquiv

theorem pull_injective (N : Submodule O (Fin r → K)) :
    Function.Injective (pull (O := O) N) := by
  intro W W' h
  apply Submodule.restrictScalars_injective O
  exact Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective _) h

theorem exists_pull (N : Submodule O (Fin r → K)) (C : Submodule O N)
    (hC : (maximalIdeal O • ⊤ : Submodule O N) ≤ C) :
    ∃ W : Submodule (ResidueField O) (Red N), pull N W = C := by
  let W : Submodule (ResidueField O) (Red N) :=
    { carrier := ((C.map (Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N)) : Submodule O (Red N)) : Set (Red N))
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := by
        intro c x hx
        obtain ⟨c, rfl⟩ := residue_surjective c
        have : residue O c • x = c • x := by
          rw [← algebraMap_smul (ResidueField O) c x]; rfl
        rw [this]
        have hx' : x ∈ C.map (Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N)) := hx
        exact (C.map (Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N))).smul_mem c hx' }
  refine ⟨W, ?_⟩
  have : W.restrictScalars O = C.map (Submodule.mkQ _) := by
    ext x; rfl
  rw [pull, this, Submodule.comap_map_mkQ, sup_eq_right.2 hC]

variable [IsFractionRing O K]

theorem map_subtype_smul_top (N : Submodule O (Fin r → K)) :
    (maximalIdeal O • ⊤ : Submodule O N).map N.subtype = maximalIdeal O • N := by
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]

def toLat (L : Lat O K r) (W : Submodule (ResidueField O) (Red L.1)) : Lat O K r :=
  ⟨(pull L.1 W).map L.1.subtype,
    { fg := by
        haveI : Module.Finite O L.1 := Module.Finite.iff_fg.2 L.2.fg
        exact (IsNoetherian.noetherian (pull L.1 W)).map _
      linearIndepOn := by
        have hfg : ((pull L.1 W).map L.1.subtype).FG := by
          haveI : Module.Finite O L.1 := Module.Finite.iff_fg.2 L.2.fg
          exact (IsNoetherian.noetherian (pull L.1 W)).map _
        exact (Submodule.IsLattice.of_fg K hfg).linearIndepOn
      span_eq_top := by
        have hle : (maximalIdeal O • L.1 : Submodule O (Fin r → K)) ≤ (pull L.1 W).map L.1.subtype := by
          rw [← map_subtype_smul_top]
          exact Submodule.map_mono (smul_top_le_pull _ _)
        rw [eq_top_iff, ← (maxMul L).2.span_eq_top]
        exact Submodule.span_mono hle }⟩

theorem toLat_injective (L : Lat O K r) : Function.Injective (toLat L) := by
  intro W W' h
  apply pull_injective L.1
  exact Submodule.map_injective_of_injective L.1.injective_subtype (congrArg Subtype.val h)

theorem card_quot_toLat [Finite (ResidueField O)] (L : Lat O K r)
    (W : Submodule (ResidueField O) (Red L.1)) :
    (toLat L W).1.toAddSubgroup.relIndex L.1.toAddSubgroup = Nat.card (Red L.1 ⧸ W) := by
  have h1 : (toLat L W).1.toAddSubgroup.relIndex L.1.toAddSubgroup
      = Nat.card (L.1 ⧸ (toLat L W).1.comap L.1.subtype) := rfl
  have h2 : (toLat L W).1.comap L.1.subtype = pull L.1 W :=
    Submodule.comap_map_eq_of_injective L.1.injective_subtype _
  rw [h1, h2, card_quot_pull]

theorem card_red [Finite (ResidueField O)] (L : Lat O K r) :
    Nat.card (Red L.1) = qRes O ^ r := by
  have hc : (maximalIdeal O • L.1).comap L.1.subtype = (maximalIdeal O • ⊤ : Submodule O L.1) := by
    rw [← map_subtype_smul_top]
    exact Submodule.comap_map_eq_of_injective L.1.injective_subtype _
  have h1 : (maxMul L).1.toAddSubgroup.relIndex L.1.toAddSubgroup
      = Nat.card (L.1 ⧸ (maximalIdeal O • L.1).comap L.1.subtype) := rfl
  rw [← relIndex_maxMul L, h1, hc]

theorem finite_red [Finite (ResidueField O)] (L : Lat O K r) : Finite (Red L.1) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_red]; exact (pow_pos (lt_of_lt_of_le two_pos two_le_qRes) _).ne')

theorem finrank_red [Finite (ResidueField O)] (L : Lat O K r) :
    Module.finrank (ResidueField O) (Red L.1) = r := by
  haveI := finite_red L
  haveI : Module.Finite (ResidueField O) (Red L.1) := Module.Finite.of_finite
  have h := card_red L
  rw [Module.natCard_eq_pow_finrank (K := ResidueField O)] at h
  exact Nat.pow_right_injective (two_le_qRes (O := O)) h

theorem ncard_subElem [Finite (ResidueField O)] (L : Lat O K r) (j : ℕ) :
    (subElem j L).ncard = Nat.card
      {W : Submodule (ResidueField O) (Red L.1) // Module.finrank (ResidueField O) (Red L.1 ⧸ W) = j} := by
  haveI := finite_red L
  have hidx : ∀ W : Submodule (ResidueField O) (Red L.1),
      (toLat L W).1.toAddSubgroup.relIndex L.1.toAddSubgroup
        = qRes O ^ Module.finrank (ResidueField O) (Red L.1 ⧸ W) := by
    intro W
    haveI : Finite (Red L.1 ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
    haveI : Module.Finite (ResidueField O) (Red L.1 ⧸ W) := Module.Finite.of_finite
    rw [card_quot_toLat, Module.natCard_eq_pow_finrank (K := ResidueField O)]
    rfl
  have hle : ∀ W : Submodule (ResidueField O) (Red L.1), (toLat L W).1 ≤ L.1 := fun W =>
    Submodule.map_subtype_le _ _
  have hlow : ∀ W : Submodule (ResidueField O) (Red L.1),
      maximalIdeal O • L.1 ≤ (toLat L W).1 := fun W => by
    rw [← map_subtype_smul_top]
    exact Submodule.map_mono (smul_top_le_pull _ _)
  let f : {W : Submodule (ResidueField O) (Red L.1) //
      Module.finrank (ResidueField O) (Red L.1 ⧸ W) = j} → subElem j L :=
    fun W => ⟨toLat L W.1, ⟨hle W.1, by rw [hidx, W.2]⟩, hlow W.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro W W' h
      exact Subtype.ext (toLat_injective L (congrArg (fun x => x.1) h))
    · rintro ⟨M, ⟨h1, h2⟩, h3⟩
      have hC : (maximalIdeal O • ⊤ : Submodule O L.1) ≤ M.1.comap L.1.subtype := by
        rw [← Submodule.map_le_iff_le_comap, map_subtype_smul_top]
        exact h3
      obtain ⟨W, hW⟩ := exists_pull L.1 _ hC
      have hM : toLat L W = M := by
        apply Subtype.ext
        change (pull L.1 W).map L.1.subtype = M.1
        rw [hW, Submodule.map_comap_subtype, inf_eq_right.2 h1]
      have hj : Module.finrank (ResidueField O) (Red L.1 ⧸ W) = j := by
        have := hidx W
        rw [hM, h2] at this
        exact (Nat.pow_right_injective (two_le_qRes (O := O)) this).symm
      exact ⟨⟨W, hj⟩, Subtype.ext hM⟩
  rw [← Nat.card_coe_set_eq]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem subElem_degrees : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (L : Lat O K r), subIdx 0 L = {L} ∧ subElem 0 L = {L} ∧ (∀ k, r < k → subElem k L = ∅) ∧
      ∀ X : ℂ, ∑ k ∈ Finset.range (r + 1), (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) *
        ((subElem k L).ncard : ℂ) * X ^ k = ∏ i ∈ Finset.range r, (1 - (qRes O : ℂ) ^ i * X) := by
  intro O K _ _ _ _ _ _ _ r L
  refine ⟨subIdx_zero L, subElem_zero L, fun k hk => subElem_eq_empty hk L, fun X => ?_⟩
  haveI := finite_red L
  haveI : Module.Finite (ResidueField O) (Red L.1) := Module.Finite.of_finite
  have h := GlobalTheory.T.qBinomial_sum_card_quotient_subspaces (ResidueField O) (Red L.1) X
  rw [finrank_red L] at h
  simp only [ncard_subElem L]
  exact h

end GlobalTheory.LatHecke
end
end

section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section
namespace GlobalTheory.EtC.Tr

theorem splits_pullbackSnd_of_splits_diagComplHom {Z X V : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f]
    (v : V ⟶ Z) (h : Splits (diagComplHom f) v) : Splits (pullback.snd f f) v := by
  obtain ⟨m, s, hs, hiso⟩ := h
  have hδs : pullback.diagonal f ≫ pullback.snd f f = 𝟙 Z := pullback.diagonal_snd f
  let t : Fin (m + 1) → (V ⟶ pullback f f) :=
    Fin.cons (α := fun _ => V ⟶ pullback f f) (v ≫ pullback.diagonal f) (fun j => s j ≫ (diagCompl f).ι)
  have ht0 : t 0 = v ≫ pullback.diagonal f := rfl
  have hts : ∀ k : Fin m, t k.succ = s k ≫ (diagCompl f).ι := fun k => rfl
  have ht : ∀ j, t j ≫ pullback.snd f f = v := by
    intro j
    induction j using Fin.cases with
    | zero => rw [ht0, Category.assoc, hδs, Category.comp_id]
    | succ k => rw [hts, Category.assoc]; exact hs k
  refine ⟨m + 1, t, ht, ?_⟩
  let d : Fin m → (V ⟶ pullback (diagComplHom f) v) :=
    fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp])
  let Φ : ∐ (fun _ : Fin m => V) ⟶ pullback (diagComplHom f) v := Sigma.desc d
  have hΦ : IsIso Φ := hiso
  have hdΦ : ∀ k, d k = Sigma.ι (fun _ : Fin m => V) k ≫ Φ := fun k => (Sigma.ι_desc _ _).symm
  let eU : pullback (diagComplHom f) v ⟶ pullback (pullback.snd f f) v :=
    pullback.map (diagComplHom f) v (pullback.snd f f) v (diagCompl f).ι (𝟙 V) (𝟙 Z)
      (by simp [diagComplHom]) (by simp)
  let eD : pullback (pullback.diagonal f ≫ pullback.snd f f) v ⟶ pullback (pullback.snd f f) v :=
    pullback.map _ v (pullback.snd f f) v (pullback.diagonal f) (𝟙 V) (𝟙 Z) (by simp) (by simp)
  let l : V ⟶ pullback (pullback.diagonal f ≫ pullback.snd f f) v :=
    pullback.lift v (𝟙 V) (by rw [hδs]; simp)
  have hl : IsIso l := by
    have h1 : IsIso (pullback.diagonal f ≫ pullback.snd f f) := by rw [hδs]; infer_instance
    have h2 : l ≫ pullback.snd _ _ = 𝟙 V := pullback.lift_snd _ _ _
    have h3 : IsIso (l ≫ pullback.snd (pullback.diagonal f ≫ pullback.snd f f) v) := by
      rw [h2]; infer_instance
    exact IsIso.of_isIso_comp_right l (pullback.snd _ _)
  let g : Fin (m + 1) → (V ⟶ pullback (pullback.snd f f) v) :=
    Fin.cons (α := fun _ => V ⟶ pullback (pullback.snd f f) v) (l ≫ eD) (fun k => d k ≫ eU)
  have hg : (Sigma.desc (fun j => pullback.lift (t j) (𝟙 V) (by rw [ht j, Category.id_comp])) :
      ∐ (fun _ : Fin (m + 1) => V) ⟶ pullback (pullback.snd f f) v) = Sigma.desc g := by
    refine Sigma.hom_ext _ _ (fun j => ?_)
    rw [Sigma.ι_desc, Sigma.ι_desc]
    induction j using Fin.cases with
    | zero =>
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        show t 0 = (l ≫ eD) ≫ _
        rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, ht0]
      · rw [pullback.lift_snd]
        show 𝟙 V = (l ≫ eD) ≫ _
        rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.id_comp]
    | succ k =>
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        show t k.succ = (d k ≫ eU) ≫ _
        rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hts]
      · rw [pullback.lift_snd]
        show 𝟙 V = (d k ≫ eU) ≫ _
        rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.id_comp]
  rw [hg]
  have hΦi : IsOpenImmersion Φ := inferInstance
  have hι : ∀ k, IsOpenImmersion (Sigma.ι (fun _ : Fin m => V) k) := fun k => inferInstance
  have hδo : IsOpenImmersion (pullback.diagonal f) := inferInstance
  have hUo : IsOpenImmersion eU := inferInstance
  have hDo : IsOpenImmersion eD := inferInstance
  have hgo : ∀ j, IsOpenImmersion (g j) := by
    intro j
    induction j using Fin.cases with
    | zero => show IsOpenImmersion (l ≫ eD); infer_instance
    | succ k => show IsOpenImmersion (d k ≫ eU); rw [hdΦ]; infer_instance
  have hgπ' : ∀ j, g j ≫ pullback.fst (pullback.snd f f) v = t j := by
    intro j
    induction j using Fin.cases with
    | zero =>
      show (l ≫ eD) ≫ _ = t 0
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, ht0]
    | succ k =>
      show (d k ≫ eU) ≫ _ = t k.succ
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hts]
  have hgπ : ∀ j y, pullback.fst (pullback.snd f f) v (g j y) = t j y := by
    intro j y
    rw [← Scheme.Hom.comp_apply, hgπ']
  have hsep : ∀ a b, pullback.diagonal f a ≠ (diagCompl f).ι b := by
    intro a b hab
    have hb : (diagCompl f).ι b ∈ Set.range (diagCompl f).ι := ⟨b, rfl⟩
    rw [Scheme.Opens.range_ι] at hb
    exact hb ⟨a, hab⟩
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨isOpenImmersion_sigmaDesc _ g ?_, ⟨fun p => ?_⟩⟩
  · intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    have hπ := congrArg (pullback.fst (pullback.snd f f) v) hy
    rw [hgπ, hgπ] at hπ
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact hij rfl
      | succ k =>
        rw [ht0, hts, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hπ
        exact hsep _ _ hπ.symm
    | succ k =>
      induction j using Fin.cases with
      | zero =>
        rw [ht0, hts, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hπ
        exact hsep _ _ hπ
      | succ k' =>
        have h1 : d k' y = d k x := by
          apply eU.isOpenEmbedding.injective
          have hy' : (d k' ≫ eU) y = (d k ≫ eU) x := hy
          rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hy'
        rw [hdΦ, hdΦ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1
        have h2 := (sigmaι_eq_iff _ _ _ _ _).mp (Φ.isOpenEmbedding.injective h1)
        exact hij (by rw [(Sigma.mk.inj_iff.mp h2).1])
  · by_cases hp : pullback.fst (pullback.snd f f) v p ∈ Set.range (pullback.diagonal f)
    · have hpD : p ∈ Set.range eD := by
        rw [Scheme.Pullback.range_map]
        exact ⟨hp, ⟨pullback.snd (pullback.snd f f) v p, rfl⟩⟩
      obtain ⟨q, rfl⟩ := hpD
      refine ⟨Sigma.ι (fun _ : Fin (m + 1) => V) 0 (inv l q), ?_⟩
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
      show (l ≫ eD) (inv l q) = eD q
      rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (inv l), IsIso.inv_hom_id]
      rfl
    · have hpU : p ∈ Set.range eU := by
        rw [Scheme.Pullback.range_map]
        refine ⟨?_, ⟨pullback.snd (pullback.snd f f) v p, rfl⟩⟩
        rw [Set.mem_preimage, Scheme.Opens.range_ι]
        exact hp
      obtain ⟨q, rfl⟩ := hpU
      obtain ⟨⟨k, x⟩, hkx⟩ := (sigmaMk (fun _ : Fin m => V)).surjective (inv Φ q)
      rw [sigmaMk_mk] at hkx
      refine ⟨Sigma.ι (fun _ : Fin (m + 1) => V) k.succ x, ?_⟩
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
      show (d k ≫ eU) x = eU q
      rw [hdΦ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hkx, ← Scheme.Hom.comp_apply (inv Φ),
        IsIso.inv_hom_id]
      rfl

end GlobalTheory.EtC.Tr
end
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem splitBy_baseChange : ∀ {Z X V T : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ} {s : Fin m → (V ⟶ Z)},
    GlobalTheory.EtC.Tr.SplitBy f y s → ∀ (w : T ⟶ V), GlobalTheory.EtC.Tr.SplitBy f (w ≫ y) (fun j => w ≫ s j) := by
  intro Z X V T f y m s ⟨hs, hiso⟩ w
  have hs' : ∀ j, (w ≫ s j) ≫ f = w ≫ y := fun j => by rw [Category.assoc, hs j]
  refine ⟨hs', ?_⟩

  let c : Cofan (fun _ : Fin m => V) :=
    Cofan.mk (pullback f y) (fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp]))
  have hc : IsColimit c := by
    haveI : IsIso ((coproductIsCoproduct (fun _ : Fin m => V)).desc c) := hiso
    exact IsColimit.ofPointIso (coproductIsCoproduct (fun _ : Fin m => V))
  let c' : Cofan (fun _ : Fin m => T) :=
    Cofan.mk (pullback f (w ≫ y)) (fun j => pullback.lift (w ≫ s j) (𝟙 T) (by rw [hs' j, Category.id_comp]))
  let g : pullback f (w ≫ y) ⟶ pullback f y :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ w) (by rw [pullback.condition, Category.assoc])
  have hg1 : g ≫ pullback.fst f y = pullback.fst f (w ≫ y) := pullback.lift_fst _ _ _
  have hg2 : g ≫ pullback.snd f y = pullback.snd f (w ≫ y) ≫ w := pullback.lift_snd _ _ _

  have hA : IsPullback (pullback.snd f (w ≫ y)) g w (pullback.snd f y) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst f y) (v₂₂ := y) (h₃₁ := f) ?_ hg2.symm
      (IsPullback.of_hasPullback f y).flip
    rw [hg1]
    exact (IsPullback.of_hasPullback f (w ≫ y)).flip
  let α : Discrete.functor (fun _ : Fin m => T) ⟶ Discrete.functor (fun _ : Fin m => V) :=
    Discrete.natTrans (fun _ => w)
  have hsq : ∀ j, w ≫ c.ι.app ⟨j⟩ = c'.ι.app ⟨j⟩ ≫ g := by
    intro j
    show w ≫ pullback.lift (s j) (𝟙 V) _ = pullback.lift (w ≫ s j) (𝟙 T) _ ≫ g
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, hg1, pullback.lift_fst]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, hg2, ← Category.assoc, pullback.lift_snd,
        Category.comp_id, Category.id_comp]
  have hcc : α ≫ c.ι = c'.ι ≫ (Functor.const _).map g := by
    ext ⟨j⟩
    exact hsq j
  have hpb : ∀ j, IsPullback (c'.ι.app j) (α.app j) g (c.ι.app j) := by
    rintro ⟨j⟩
    refine IsPullback.of_right (h₁₂ := pullback.snd f (w ≫ y)) (v₁₃ := w) (h₂₂ := pullback.snd f y) ?_ (hsq j).symm hA
    have e1 : c'.ι.app ⟨j⟩ ≫ pullback.snd f (w ≫ y) = 𝟙 T := pullback.lift_snd _ _ _
    have e2 : c.ι.app ⟨j⟩ ≫ pullback.snd f y = 𝟙 V := pullback.lift_snd _ _ _
    rw [e1, e2]
    show IsPullback (𝟙 T) w w (𝟙 V)
    exact IsPullback.id_horiz w
  obtain ⟨hc'⟩ := FinitaryPreExtensive.isUniversal_finiteCoproducts hc c' α g hcc
    (NatTrans.Equifibered.of_discrete _) hpb
  have : Sigma.desc (fun j => pullback.lift (w ≫ s j) (𝟙 T) (by rw [hs' j, Category.id_comp])) =
      ((coproductIsCoproduct (fun _ : Fin m => T)).coconePointUniqueUpToIso hc').hom := by
    apply Sigma.hom_ext; intro j
    rw [Sigma.ι_desc]
    exact ((coproductIsCoproduct (fun _ : Fin m => T)).comp_coconePointUniqueUpToIso_hom hc' ⟨j⟩).symm
  rw [this]
  infer_instance

end GlobalTheory.EtC.Tr
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem splits_of_isEmpty_pullback : ∀ {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X),
    IsEmpty (pullback f y : Scheme.{0}) → GlobalTheory.EtC.Tr.Splits f y := by
  intro Z X V f y hE
  have hP : IsInitial (pullback f y) := isInitialOfIsEmpty
  refine ⟨0, Fin.elim0, fun j => j.elim0, ?_⟩
  refine ⟨⟨hP.to _, ?_, hP.hom_ext _ _⟩⟩
  apply Sigma.hom_ext
  intro j
  exact j.elim0

end GlobalTheory.EtC.Tr
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut

theorem _root_.GlobalTheory.T.rightTranslationSum_scalar_isotypic : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ), (∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f) → ∀ f ∈ Formalism.L2.NG.isoTyp a.ρ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  first | exact @GlobalTheory.SumTransIso.sumRt_isoTyp | exact GlobalTheory.SumTransIso.sumRt_isoTyp | (intros; apply GlobalTheory.SumTransIso.sumRt_isoTyp <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (Formalism.AUTREP.GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), Formalism.L2.NG.HypOutside J χ B → ∀ (s : ReciprocityTheory.Aut.SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → Formalism.AUTREP.IsUnif L s.v ϖ → ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Formalism.AUTREP.tSet L n s ϖ k).Finite := by
  first | exact @GlobalTheory.TSetFin.finite_image_tSet | exact GlobalTheory.TSetFin.finite_image_tSet | (intros; apply GlobalTheory.TSetFin.finite_image_tSet <;> assumption)
end

section

open Formalism.UG Matrix

theorem _root_.GlobalTheory.T.uniformizerPowerTorus_mem_normal_unitarySubgroup : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ N : Subgroup (Formalism.UG.GU σ n), N.Normal → Formalism.UG.KU σ n ≤ N → (∀ u : Formalism.UG.GU σ n, Formalism.UG.IsUnipU u → u ∈ N) → ∀ (c : Fin n → ℤ), (∀ i : Fin n, c i.rev = -c i) → ∀ t : Formalism.UG.GU σ n, ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => ϖ ^ c i) → t ∈ N := by
  first | exact @GlobalTheory.torus_mem_normal | exact GlobalTheory.torus_mem_normal | (intros; apply GlobalTheory.torus_mem_normal <;> assumption)
end
