module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Formalism.SatakeDualWeyl.Statement
public import Mathlib.RepresentationTheory.Irreducible
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
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
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle307
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.ComplOffPlace

open IsDedekindDomain
open scoped TensorProduct

private theorem valued_v_coe_inv_le_one_of_not_mem {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E))
    {x : 𝓞 E} (hx : x ∉ Q.asIdeal) : Valued.v ((((x : E)⁻¹ : E)) : Q.adicCompletion E) ≤ 1 := by
  rw [HeightOneSpectrum.adicCompletion.valued_coe, map_inv₀, RingOfIntegers.coe_eq_algebraMap,
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (v := Q) (K := E)).mpr hx, inv_one]

private theorem adicCompletion_coe_inv_mul_coe {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E))
    {x : E} (hx : x ≠ 0) : ((x⁻¹ : E) : Q.adicCompletion E) * ((x : E) : Q.adicCompletion E) = 1 := by
  rw [← HeightOneSpectrum.adicCompletion.coe_mul, inv_mul_cancel₀ hx, HeightOneSpectrum.adicCompletion.coe_one]

theorem exists_comb {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (f : FiniteAdeleRing (𝓞 E) E) (h1 : f P = 1) (h0 : ∀ Q, Q ≠ P → f Q = 0) :
    ∃ x ∈ P.asIdeal, ∃ y ∈ P.asIdeal, ∃ b c : FiniteAdeleRing (𝓞 E) E, (∀ Q, Valued.v (b Q) ≤ 1) ∧
      (∀ Q, Valued.v (c Q) ≤ 1) ∧
      1 - f = b * algebraMap E _ (x : E) + c * algebraMap E _ (y : E) := by
  classical
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot

  have hfin : {Q : HeightOneSpectrum (𝓞 E) | Q.asIdeal ∣ Ideal.span {x}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])

  have hcov : ¬ ((P.asIdeal : Set (𝓞 E)) ⊆
      ⋃ Q ∈ ((hfin.toFinset.erase P : Finset (HeightOneSpectrum (𝓞 E))) : Set (HeightOneSpectrum (𝓞 E))),
        ((fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) Q : Set (𝓞 E))) := by
    rw [Ideal.subset_union_prime (f := fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) P P
      (fun Q _ _ _ => Q.isPrime)]
    rintro ⟨Q, hQS, hle⟩
    exact (Finset.mem_erase.mp hQS).1
      (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hle).symm)
  obtain ⟨y, hyP, hyS⟩ := Set.not_subset.mp hcov
  have hy : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → x ∈ Q.asIdeal → y ∉ Q.asIdeal := by
    intro Q hQ hxQ hyQ
    apply hyS
    refine Set.mem_biUnion (x := Q) ?_ hyQ
    rw [Finset.coe_erase, Set.mem_diff, Set.Finite.coe_toFinset]
    exact ⟨Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hxQ), hQ⟩

  let bf : ∀ Q : HeightOneSpectrum (𝓞 E), Q.adicCompletion E := fun Q =>
    if Q = P then 0 else if x ∈ Q.asIdeal then 0 else (((x : E)⁻¹ : E) : Q.adicCompletion E)
  let cf : ∀ Q : HeightOneSpectrum (𝓞 E), Q.adicCompletion E := fun Q =>
    if Q = P then 0 else if x ∈ Q.asIdeal then (((y : E)⁻¹ : E) : Q.adicCompletion E) else 0
  have hbf : ∀ Q, Valued.v (bf Q) ≤ 1 := by
    intro Q
    show Valued.v (if Q = P then 0 else if x ∈ Q.asIdeal then 0 else (((x : E)⁻¹ : E) : Q.adicCompletion E)) ≤ 1
    split_ifs with h1 h2
    · simp
    · simp
    · exact valued_v_coe_inv_le_one_of_not_mem Q h2
  have hcf : ∀ Q, Valued.v (cf Q) ≤ 1 := by
    intro Q
    show Valued.v (if Q = P then 0 else if x ∈ Q.asIdeal then (((y : E)⁻¹ : E) : Q.adicCompletion E) else 0) ≤ 1
    split_ifs with h1 h2
    · simp
    · exact valued_v_coe_inv_le_one_of_not_mem Q (hy Q h1 h2)
    · simp
  let b : FiniteAdeleRing (𝓞 E) E := Subtype.mk bf (Filter.Eventually.of_forall hbf)
  let c : FiniteAdeleRing (𝓞 E) E := Subtype.mk cf (Filter.Eventually.of_forall hcf)
  refine ⟨x, hxP, y, hyP, b, c, hbf, hcf, ?_⟩
  ext1 Q
  show (1 : Q.adicCompletion E) - f Q = bf Q * ((x : E) : Q.adicCompletion E) + cf Q * ((y : E) : Q.adicCompletion E)
  by_cases hQ : Q = P
  · subst hQ
    simp [bf, cf, h1]
  · have hxQ' : ∀ hxQ : x ∉ Q.asIdeal, (x : E) ≠ 0 := fun hxQ h =>
      hxQ (by rw [show x = 0 from by exact_mod_cast h]; exact Q.asIdeal.zero_mem)
    by_cases hxQ : x ∈ Q.asIdeal
    · have hyQ := hy Q hQ hxQ
      have hy0 : (y : E) ≠ 0 := fun h =>
        hyQ (by rw [show y = 0 from by exact_mod_cast h]; exact Q.asIdeal.zero_mem)
      simp only [bf, cf, if_neg hQ, if_pos hxQ, h0 Q hQ, sub_zero, zero_mul, zero_add]
      exact (adicCompletion_coe_inv_mul_coe Q hy0).symm
    · simp only [bf, cf, if_neg hQ, if_neg hxQ, h0 Q hQ, sub_zero, zero_mul, add_zero]
      exact (adicCompletion_coe_inv_mul_coe Q (hxQ' hxQ)).symm

theorem mul_smul_mem_hat (D : D7) {n : ℕ} (I : Ideal (𝓞 D.host.E)) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D) {t : 𝓞 D.host.E} (ht : t ∈ I)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    (a * (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (t : D.host.E)) • y ∈
      GlobalTheory.AdLat.hat D.host.F ((I • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) := by
  unfold intAE at ha
  unfold GlobalTheory.AdLat.hat at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    induction ha using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, s, rfl⟩ := hw
      refine AddSubgroup.subset_closure ⟨c * b, fun v => mul_mem (hc v) (hb v),
        (s * t) • x, Submodule.smul_mem_smul (I.mul_mem_left s ht) hx, ?_⟩
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def,
        map_mul, ← RingOfIntegers.coe_eq_algebraMap]
    | zero => simp
    | add u w _ _ hu hw =>
      rw [add_mul, add_smul]
      exact AddSubgroup.add_mem _ hu hw
    | neg u _ hu =>
      rw [neg_mul, neg_smul]
      exact AddSubgroup.neg_mem _ hu
  | zero =>
    rw [smul_zero]
    exact AddSubgroup.zero_mem _
  | add u w _ _ hu hw =>
    rw [smul_add]
    exact AddSubgroup.add_mem _ hu hw
  | neg u _ hu =>
    rw [smul_neg]
    exact AddSubgroup.neg_mem _ hu

theorem one_sub_smul_mem : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (n : ℕ) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)),
      (1 - finPart D e) • y ∈ GlobalTheory.AdLat.hat D.host.F ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) := by
  intro D P e n L he y hy
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, h1, h0⟩ := GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ he
  obtain ⟨x, hx, x', hx', b, c, hb, hc, hbc⟩ := exists_comb P (Φ e) h1 h0
  obtain ⟨zb, -, hzb⟩ := hΦ.surj b
  obtain ⟨zc, -, hzc⟩ := hΦ.surj c
  have hzbi : finPart D zb ∈ intAE D := (hΦ.int zb).mpr fun Q => by rw [hzb]; exact hb Q
  have hzci : finPart D zc ∈ intAE D := (hΦ.int zc).mpr fun Q => by rw [hzc]; exact hc Q

  set s : AE D := (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E) with hs
  have hsi : infPart D s = 0 := by
    rw [hs]
    show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  have hsf : finPart D s = 1 := by
    rw [hs]
    show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E)) = 1
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact Algebra.TensorProduct.one_def.symm
  have hinc : ∀ z : D.host.E, finPart D (incA D z) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] z := by
    intro z
    show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] z) = _
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  have key : (1 - e) * s = (zb * incA D (x : D.host.E) + zc * incA D (x' : D.host.E)) * s := by
    apply hΦ.ext'
    · simp only [map_mul, hsi, mul_zero]
    · intro Q
      have hΦe : Φ ((1 - e) * s) = Φ ((zb * incA D (x : D.host.E) + zc * incA D (x' : D.host.E)) * s) := by
        simp only [map_mul, map_sub, map_one, map_add (f := _), hΦ.inc, hzb, hzc, hbc]
      rw [hΦe]
  have key' : 1 - finPart D e =
      finPart D zb * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x : D.host.E)) +
        finPart D zc * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x' : D.host.E)) := by
    have h := congrArg (finPart D) key
    simpa only [map_mul, map_sub, map_one, map_add (f := _), hsf, mul_one, hinc] using h
  rw [key', add_smul]
  exact AddSubgroup.add_mem _ (mul_smul_mem_hat D P.asIdeal L hzbi hx hy)
    (mul_smul_mem_hat D P.asIdeal L hzci hx' hy)

end GlobalTheory.ComplOffPlace
end
end

section

noncomputable section

namespace GlobalTheory.LFun.HeckeScalar

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LFun.SatCompare

variable {G V M : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
  {ρ : Representation ℂ G V} {K : Subgroup G} {x : V}

def finOrbit (τ : Representation ℂ G M) (K : Subgroup G) : Submodule ℂ M where
  carrier := {m | (Set.range fun k : K => τ k m).Finite}
  zero_mem' := (Set.finite_singleton 0).subset (by rintro _ ⟨k, rfl⟩; simp)
  add_mem' {a b} ha hb := (Set.Finite.add ha hb).subset (by
    rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, _, ⟨k, rfl⟩, by simp⟩)
  smul_mem' c a ha := (Set.Finite.image (c • ·) ha).subset (by
    rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, by simp⟩)

private theorem mem_fixed_iff_twisted_operators {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ G W)
    (L : Subgroup G) (v : W) : v ∈ fixed τ L ↔ ∀ k : L, τ k v = v := by
  change (∀ k : L, τ k v = ((1 : L →* ℂˣ) k : ℂ) • v) ↔ _
  simp

theorem exists_fixed_preimage {τ : Representation ℂ G M} (π : M →ₗ[ℂ] V) (hπ : ∀ g m, π (τ g m) = ρ g (π m))
    {m : M} (hm : m ∈ finOrbit τ K) (hy : π m ∈ fixed ρ K) : ∃ m' ∈ fixed τ K, π m' = π m := by
  classical

  have hfin : (Set.range fun k : K => τ k m).Finite := hm
  obtain ⟨O, hO⟩ : ∃ O : Finset M, ∀ o, o ∈ O ↔ ∃ k : K, τ k m = o :=
    ⟨hfin.toFinset, fun o => by rw [Set.Finite.mem_toFinset]; try exact Iff.rfl⟩
  have hmul : ∀ (a b : K) (o : M), τ (a : G) (τ (b : G) o) = τ ((a * b : K) : G) o := by
    intro a b o
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  have hperm : ∀ a : K, ∑ o ∈ O, τ (a : G) o = ∑ o ∈ O, o := by
    intro a
    refine Finset.sum_nbij' (fun o => τ (a : G) o) (fun o => τ ((a⁻¹ : K) : G) o) ?_ ?_ ?_ ?_ ?_
    · intro o ho
      obtain ⟨k, rfl⟩ := (hO o).1 ho
      exact (hO _).2 ⟨a * k, (hmul a k m).symm⟩
    · intro o ho
      obtain ⟨k, rfl⟩ := (hO o).1 ho
      exact (hO _).2 ⟨a⁻¹ * k, (hmul a⁻¹ k m).symm⟩
    · intro o _
      show τ ((a⁻¹ : K) : G) (τ (a : G) o) = o
      rw [hmul, inv_mul_cancel]
      simp
    · intro o _
      show τ (a : G) (τ ((a⁻¹ : K) : G) o) = o
      rw [hmul, mul_inv_cancel]
      simp
    · intro o _
      rfl
  have hne : (O.card : ℂ) ≠ 0 := by
    have hm' : m ∈ O := (hO m).2 ⟨1, by simp⟩
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hm')
  refine ⟨(O.card : ℂ)⁻¹ • ∑ o ∈ O, o, ?_, ?_⟩
  · rw [mem_fixed_iff_twisted_operators]
    intro a

    rw [map_smul, map_sum, hperm a]
  · have hconst : ∀ o ∈ O, π o = π m := by
      intro o ho
      obtain ⟨k, rfl⟩ := (hO o).1 ho
      rw [hπ]
      exact (mem_fixed_iff_twisted_operators ρ K (π m)).1 hy k

    rw [map_smul, map_sum, Finset.sum_congr rfl hconst, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ hne, one_smul]

def permRep (K : Subgroup G) : Representation ℂ G (G ⧸ K →₀ ℂ) where
  toFun g := Finsupp.lmapDomain ℂ ℂ (g • ·)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_smul]

theorem permRep_single (g : G) (c : G ⧸ K) (a : ℂ) :
    permRep K g (Finsupp.single c a) = Finsupp.single (g • c) a := by
  change Finsupp.mapDomain (g • ·) (Finsupp.single c a) = _
  exact Finsupp.mapDomain_single

private theorem permRep_apply_eq_mapDomain (g : G) (φ : G ⧸ K →₀ ℂ) :
    permRep K g φ = Finsupp.mapDomain (g • ·) φ :=
  rfl

theorem permRep_apply (g : G) (φ : G ⧸ K →₀ ℂ) (c : G ⧸ K) : permRep K g φ (g • c) = φ c := by
  rw [permRep_apply_eq_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective (MulAction.injective g) φ c

theorem mem_finOrbit (hK : IsCommensurated K) (φ : G ⧸ K →₀ ℂ) : φ ∈ finOrbit (permRep K) K := by
  classical

  have hpi : (Set.pi Set.univ fun c : φ.support => MulAction.orbit K (c : G ⧸ K)).Finite := by
    refine Set.Finite.pi fun c => ?_
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (c : G ⧸ K)
    rw [← hs]
    exact Formalism.UG.P.orbit_coset_finite K hK s
  change (Set.range fun k : K => permRep K k φ).Finite
  refine (hpi.image fun t => ∑ c : φ.support, Finsupp.single (t c) (φ c)).subset ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨fun c => k • (c : G ⧸ K), ?_, ?_⟩
  · rw [Set.mem_univ_pi]
    intro c
    exact MulAction.mem_orbit _ k
  · show (∑ c : φ.support, Finsupp.single (k • (c : G ⧸ K)) (φ c)) = permRep K (k : G) φ
    rw [permRep_apply_eq_mapDomain]
    exact Finset.sum_coe_sort φ.support fun a => Finsupp.single ((k : G) • a) (φ a)

def orbitMap (ρ : Representation ℂ G V) (K : Subgroup G) (x : V) : (G ⧸ K →₀ ℂ) →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ fun c => ρ c.out x

theorem orbitMap_single (hx : x ∈ fixed ρ K) (g : G) (a : ℂ) :
    orbitMap ρ K x (Finsupp.single (g : G ⧸ K) a) = a • ρ g x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (s := K) g
  simp only [orbitMap, Finsupp.linearCombination_single]
  rw [hk, map_mul, Module.End.mul_apply, (mem_fixed_iff_twisted_operators ρ K x).1 hx k]

theorem orbitMap_permRep (hx : x ∈ fixed ρ K) (g : G) (φ : G ⧸ K →₀ ℂ) :
    orbitMap ρ K x (permRep K g φ) = ρ g (orbitMap ρ K x φ) := by
  induction φ using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add φ₁ φ₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
  | single c a =>
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
    rw [permRep_single, MulAction.Quotient.smul_mk, smul_eq_mul, orbitMap_single hx, orbitMap_single hx, map_smul,
      map_mul, Module.End.mul_apply]

theorem orbitMap_surjective (hρ : ρ.IsIrreducible) (hx : x ∈ fixed ρ K) (h0 : x ≠ 0) :
    Function.Surjective (orbitMap ρ K x) := by

  let S : Subrepresentation ρ := ⟨LinearMap.range (orbitMap ρ K x), by
    intro g v hv
    obtain ⟨φ, rfl⟩ := LinearMap.mem_range.1 hv
    exact LinearMap.mem_range.2 ⟨permRep K g φ, orbitMap_permRep hx g φ⟩⟩
  have hxS : x ∈ S.toSubmodule := by
    show x ∈ LinearMap.range (orbitMap ρ K x)
    refine LinearMap.mem_range.2 ⟨Finsupp.single ((1 : G) : G ⧸ K) 1, ?_⟩
    rw [orbitMap_single hx, one_smul, map_one, Module.End.one_apply]
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  rcases eq_bot_or_eq_top S with h | h
  · rw [h] at hxS
    exact absurd ((Submodule.mem_bot ℂ).1 hxS) h0
  · intro y
    have hy : y ∈ S.toSubmodule := by
      rw [h]
      exact Submodule.mem_top
    exact LinearMap.mem_range.1 hy

end GlobalTheory.LFun.HeckeScalar

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimeSize

theorem k_pow_le_g {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (i : Fin 2) : D.R.k ^ 8 ≤ D.host.g i := by
  obtain ⟨Y, h1, -, -, h4⟩ := P.g_Y
  have hL : 0 ≤ L.sc.L := by
    unfold Scale.L; exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
  have hb : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp hL
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h2 : (D.R.k : ℝ) ≤ D.R.k * L.sc.b := le_mul_of_one_le_right hk hb
  have h3 : (D.R.k : ℝ) ^ 8 ≤ (D.R.k * L.sc.b) ^ 8 := pow_le_pow_left₀ hk h2 8
  have : (D.R.k : ℝ) ^ 8 ≤ D.host.g i := h3.trans (h1.trans (h4 i).1)
  exact_mod_cast this

theorem typePrime_large_and_ok : ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → ∀ k : Fin 2,
    Module.finrank ℚ D.host.E * D.R.r + 1 < D.host.g k ∧
      GlobalTheory.BadShare.PrimeOK (D.host.g k) D.host.q D.host.d := by
  intro D L P i
  have hg := k_pow_le_g P i
  have hE : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have he := D.host.two_le_e
  have h4 : 2 ^ 2 ≤ 2 ^ D.R.e := Nat.pow_le_pow_right (by norm_num) he
  have hf := D.R.f_le_k
  have hfo : D.R.f = 2 * D.R.ord := rfl
  have ho : 2 ^ D.R.e ≤ D.R.ord := Nat.le_of_dvd D.R.ord_pos D.R.toFrame.two_pow_dvd_ord
  have hm := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have ht := D.R.rank_add_five_le
  have hk8 : 8 ≤ D.R.k := by omega
  have hr : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hE' : Module.finrank ℚ D.host.E ≤ 2 * D.R.k := by
    have h2f : D.R.f = 2 * D.R.ord := rfl
    have hfk : D.R.f ≤ D.R.k := hf
    omega
  have hk6 : 8 ^ 6 ≤ D.R.k ^ 6 := Nat.pow_le_pow_left hk8 6
  have hk2 : 8 ^ 2 ≤ D.R.k ^ 2 := Nat.pow_le_pow_left hk8 2
  have hpow : 8 ^ 6 * D.R.k ^ 2 ≤ D.R.k ^ 8 := by
    calc 8 ^ 6 * D.R.k ^ 2 ≤ D.R.k ^ 6 * D.R.k ^ 2 := Nat.mul_le_mul_right _ hk6
      _ = D.R.k ^ 8 := by ring
  have hprod : Module.finrank ℚ D.host.E * D.R.r ≤ 4 * D.R.k ^ 2 := by
    calc Module.finrank ℚ D.host.E * D.R.r ≤ (2 * D.R.k) * (2 * D.R.k) := Nat.mul_le_mul hE' hr
      _ = 4 * D.R.k ^ 2 := by ring
  obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
  have hb := D.host.qd_big.1
  refine ⟨by omega, hq, hd, by omega, by omega, by omega, ?_, ?_, by omega⟩
  · have h1 : 5 * 1 ≤ D.R.t * D.R.r := Nat.mul_le_mul (by omega) hr1
    have h2 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r) := by ring
    exact le_max_of_le_left (by omega)
  · have hc := D.ntypes.g_cond i
    have hdvd : 16 * D.host.q * D.host.d ∣ D.host.QS * D.host.q * D.host.d := by
      have h16 : 16 ∣ D.host.QS := (pow_dvd_pow 2 (by omega : 4 ≤ D.R.e + 2)).trans D.host.tower_dvd
      exact Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right h16 _) _
    refine hdvd.trans ⟨D.host.g i / (D.host.QS * D.host.q * D.host.d), ?_⟩
    have := Nat.div_add_mod (D.host.g i) (D.host.QS * D.host.q * D.host.d)
    omega

end GlobalTheory.TypePrimeSize
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain

theorem exists_intertwiner_of_index_eq {D : D7} (hP : ItPair D) (k : Fin D.R.m) (hk : ChainPar D k)
    (V W : HSp D) (a b : ℕ) (ha : a = k) (hb : b = k + 1)
    (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) b))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (hθ : IsInfFam θ) :
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M,
      ∀ ω f, IsStepWeil k ψ V W ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  subst ha hb
  obtain ⟨It, -, hIt⟩ := hP k V W M M' θ ψ hθ hk
  exact ⟨It, hIt⟩

theorem innerIntertwiners_of_pair (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (hP : ItPair D) (hC : ∀ k, ChainPar D k) (hθ : IsInfFam R.θ) (hS : StepsOK R) :
    ItYSt R := by
  intro k hk
  have hk0 : k < D.R.m := Nat.lt_of_succ_lt hk
  obtain ⟨It, hIt⟩ := exists_intertwiner_of_index_eq hP ⟨k, hk0⟩ (hC _) (Yc D k) (Yc D (k + 1))
    (min k D.R.m) (min (k + 1) D.R.m) (Nat.min_eq_left hk0.le) (Nat.min_eq_left hk.le)
    (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ
  refine ⟨It, fun t => ?_⟩
  obtain ⟨hω, hv⟩ := hS.1 t ⟨k, hk0⟩ hk
  exact hIt _ _ hω hv

end GlobalTheory.Chain
end
