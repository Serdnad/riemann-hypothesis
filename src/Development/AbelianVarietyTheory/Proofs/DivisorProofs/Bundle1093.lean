module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle822
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle997
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle396
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
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
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory

namespace SecLocalCondition

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

variable {W : Scheme.{0}} [IsIntegral W] {H : LB W}

theorem gen_mem_nonzeroLocus_iff {n : ℕ} (s : (lbPow H n).Sec) {J : PUnit → H.ι}
    (hJ : genericPoint W ∈ powChart H J) :
    genericPoint W ∈ nonzeroLocus s ↔ fnOf _ hJ (powFn s J) ≠ 0 := by
  refine (mem_nonzeroLocus_iff_powFn s hJ).trans ((LBGerm.isUnit_gs_iff (𝟙 W) (genericPoint W) (powChart H J) hJ (powFn s J)).trans ?_)
  change genericPoint W ∈ W.basicOpen (powFn s J) ↔ _
  rw [← unitAt_fnOf_iff hJ hJ]
  exact ⟨UnitAt.ne_zero, unitAt_genericPoint⟩

theorem regAt_pow {x : W} {f : W.functionField} (h : RegAt x f) (k : ℕ) : RegAt x (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ k ih => rw [pow_succ]; exact ih.mul h

theorem exists_local (hA : IsAmpleLB H) (P : W → W.functionField → Prop)
    (hP : ∀ y c c', P y c → RegAt y c' → P y (c' * c)) {y : W} {V : W.Opens} (hy : y ∈ V) (d : Γ(W, V))
    (hd : fnOf V (gen_mem hy) d ≠ 0) (hPd : ∀ y' ∈ V, P y' (fnOf V (gen_mem hy) d)) :
    ∃ m, 1 ≤ m ∧ ∃ u : (lbPow H m).Sec, ∃ O : W.Opens, y ∈ O ∧ genericPoint W ∈ nonzeroLocus u ∧
      ∀ y' ∈ O, ∀ (i : (lbPow H m).ι) (hi : y' ∈ (lbPow H m).U i), P y' (fnOf _ (gen_mem hi) (u.f i)) := by
  have := hA.compactSpace
  have := hA.quasiSeparatedSpace
  obtain ⟨q, hq, s, hys, hle, -⟩ := hA.exists_affine_le hy
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul (m := 0) hA.isLB s
    (fun J => resG W (inf_le_left.trans hle : nonzeroLocus s ⊓ powChart H J ≤ V) d)
    (LBGerm.mem_secOn_of_germ (M := lbPow H 0) _ fun z J J' hs hJ hJ' => by
      rw [gm_lbPow_g 0 (𝟙 W) z J J' hJ hJ', pow_zero, Units.val_one, one_mul]
      exact (gs_res (𝟙 W) z (inf_le_left.trans hle : nonzeroLocus s ⊓ powChart H J ≤ V) ⟨hs, hJ⟩ d).trans
        (gs_res (𝟙 W) z (inf_le_left.trans hle : nonzeroLocus s ⊓ powChart H J' ≤ V) ⟨hs, hJ'⟩ d).symm)
  obtain ⟨u, hu⟩ := hN (N + 1) (Nat.le_succ N)
  have key : ∀ (J : PUnit → H.ι) (hJ : genericPoint W ∈ powChart H J),
      fnOf _ hJ (powFn u J) = fnOf _ hJ (powFn s J) ^ (N + 1) * fnOf V (gen_mem hy) d := by
    intro J hJ
    have hη : genericPoint W ∈ nonzeroLocus s ⊓ powChart H J := ⟨gen_mem hys, hJ⟩
    have e := congrArg (fnOf _ hη) (hu J)
    rwa [map_mul, map_pow, fnOf_resG, fnOf_resG, fnOf_resG] at e
  refine ⟨0 + q * (N + 1), by nlinarith, u, _, hys, ?_, fun y' hy' i hi => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_chart (isLB_lbPow hA.isLB q) (genericPoint W)
    rw [gen_mem_nonzeroLocus_iff u hJ, key J hJ]
    exact mul_ne_zero (pow_ne_zero _ ((gen_mem_nonzeroLocus_iff s hJ).1 (gen_mem hys))) hd
  · have hr : RegAt y' (fnOf _ (gen_mem hi) (powFn s i) ^ (N + 1)) :=
      regAt_pow (regAt_fnOf hi (gen_mem hi) (powFn s i)) (N + 1)
    have e : fnOf _ (gen_mem hi) (u.f i) = _ := key i (gen_mem hi)
    rw [e]
    exact hP y' _ _ (hPd y' (hle hy')) hr

theorem exists_prod (hL : H.IsLB) (P : W → W.functionField → Prop)
    (hP : ∀ y c c', P y c → RegAt y c' → P y (c' * c)) {ι : Type} (m : ι → ℕ) (hm : ∀ a, 1 ≤ m a)
    (u : ∀ a, (lbPow H (m a)).Sec) (hu : ∀ a, genericPoint W ∈ nonzeroLocus (u a)) (Q : ι → W → Prop)
    (hQ : ∀ a y', Q a y' → ∀ (i : (lbPow H (m a)).ι) (hi : y' ∈ (lbPow H (m a)).U i),
      P y' (fnOf _ (gen_mem hi) ((u a).f i))) (T : Finset ι) :
    ∃ n, (T.Nonempty → 1 ≤ n) ∧ ∃ t : (lbPow H n).Sec, genericPoint W ∈ nonzeroLocus t ∧
      ∀ a ∈ T, ∀ y', Q a y' → ∀ (i : (lbPow H n).ι) (hi : y' ∈ (lbPow H n).U i),
        P y' (fnOf _ (gen_mem hi) (t.f i)) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨0, fun h => absurd h Finset.not_nonempty_empty, secOfFn H 1, ?_, fun a ha => absurd ha (Finset.notMem_empty a)⟩
    rw [nonzeroLocus_secOfFn hL, Scheme.basicOpen_one]
    trivial
  | insert b T hb ih =>
    obtain ⟨n, -, t, ht, htP⟩ := ih
    refine ⟨m b + n, fun _ => le_add_right (hm b), secMul (u b) t,
      (nonzeroLocus_secMul (u b) t).ge ⟨hu b, ht⟩, fun a ha y' hy' i hi => ?_⟩
    have e : fnOf _ (gen_mem hi) ((secMul (u b) t).f i) =
        fnOf _ (gen_mem hi) ((u b).f i) * fnOf _ (gen_mem hi) (t.f i) :=
      map_mul (fnOf _ (gen_mem hi)) ((u b).f i) (t.f i)
    rw [e]
    rcases Finset.mem_insert.1 ha with rfl | ha
    · rw [mul_comm]
      exact hP y' _ _ (hQ a y' hy' i hi) (regAt_fnOf hi (gen_mem hi) _)
    · exact hP y' _ _ (htP a ha y' hy' i hi) (regAt_fnOf hi (gen_mem hi) _)

end SecLocalCondition


open SecLocalCondition in
theorem exists_sec_forall_local_condition : ∀ (W : Scheme.{0}) [IsIntegral W] (H : LB W), IsAmpleLB H →
    ∀ (P : W → W.functionField → Prop), (∀ y c c', P y c → RegAt y c' → P y (c' * c)) →
    (∀ y, ∃ (V : W.Opens) (hy : y ∈ V) (d : Γ(W, V)), fnOf V (gen_mem hy) d ≠ 0 ∧
      ∀ y' ∈ V, P y' (fnOf V (gen_mem hy) d)) →
    ∃ n, 1 ≤ n ∧ ∃ t : (lbPow H n).Sec, t ≠ 0 ∧
      ∀ (y : W) (i : (lbPow H n).ι) (hi : y ∈ (lbPow H n).U i), P y (fnOf _ (gen_mem hi) (t.f i)) := by
  intro W _ H hA P hP hloc
  have := hA.compactSpace
  choose V hy d hd hPd using hloc
  choose m hm u O hyO hu hQ using fun y => exists_local hA P hP (hy y) (d y) (hd y) (hPd y)
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top O hyO
  obtain ⟨n, hn, t, ht, htP⟩ := exists_prod hA.isLB P hP m hm u hu (fun a y' => y' ∈ O a) hQ T
  refine ⟨n, hn ?_, t, (sec_ne_zero_iff t).2 ht, fun y i hi => ?_⟩
  · obtain ⟨a, -⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ (genericPoint W)))
    exact ⟨a, a.2⟩
  · obtain ⟨a, ha⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ y))
    exact htP a a.2 y ha i hi

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn.Inhab

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Chr
open scoped Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isConjPl_iff_conjPl {w w' : HeightOneSpectrum (𝓞 D.host.E)} :
    Lev.IsConjPl w w' ↔ ConjPl D.host.conj.toRingEquiv w w' := by
  rw [conjPl_iff_smul]
  constructor
  · intro hc
    have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
      intro y hy
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
      obtain ⟨z, hz, hzv⟩ := hc _ hy
      have e : z = y := RingOfIntegers.ext
        ((hzv.trans (bridge_star_holds D.R D.host _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
      exact e ▸ hz
    obtain ⟨v, hv, -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv w
    have hv' := (conjPl_iff_smul D.host.conj w v).1 hv
    have hvw : v = w' := HeightOneSpectrum.ext (v.isMaximal.eq_of_le w'.isPrime.ne_top (hv' ▸ hle))
    exact hvw ▸ hv'
  · intro h c hc
    exact ⟨D.host.conj • c, h ▸ Ideal.smul_mem_pointwise_smul _ _ _ hc, (bridge_star_holds D.R D.host _).symm⟩

theorem mem_aboveK {P : HeightOneSpectrum (𝓞 D.host.K)} {w : HeightOneSpectrum (𝓞 D.host.E)} :
    w ∈ GlobalTheory.Mem.Chr.aboveF (L := D.host.E) D.host.K P ↔ w.under (𝓞 D.host.K) = P := by
  simp [GlobalTheory.Mem.Chr.aboveF]

theorem overP_of_under {p : ℕ} {P : HeightOneSpectrum (𝓞 D.host.K)} (hP : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.K) = P) : GlobalTheory.Mem.Chr.OverP D.host p w := by
  subst h
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((p : ℕ) : 𝓞 D.host.K) ∈ w.asIdeal := hP
  rwa [map_natCast] at h2

section One

variable {p : ℕ} (hp : p.Prime) (hs : SplitsC D.host.E p) {P : HeightOneSpectrum (𝓞 D.host.K)}
  (hP : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal)
include hp hs hP

theorem overP_iff (w : HeightOneSpectrum (𝓞 D.host.E)) : GlobalTheory.Mem.Chr.OverP D.host p w ↔
    w ∈ GlobalTheory.Mem.Chr.aboveF (L := D.host.E) D.host.K P ∨ ∃ w' ∈ GlobalTheory.Mem.Chr.aboveF (L := D.host.E) D.host.K P, Lev.IsConjPl w' w := by
  constructor
  · intro hw
    by_cases h : w.under (𝓞 D.host.K) = P
    · exact Or.inl (mem_aboveK.2 h)
    · obtain ⟨w', hw', -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv.symm w
      have hc : ConjPl D.host.conj.toRingEquiv w' w := fun x => by
        have := hw' (D.host.conj.toRingEquiv x)
        rw [RingEquiv.symm_apply_apply] at this
        exact this.symm
      have ho : GlobalTheory.Mem.Chr.OverP D.host p w' := ((conjPl_iff_mem _ w' w).1 hc _ _ (by simp)).2 hw
      exact Or.inr ⟨w', mem_aboveK.2 (((splitsC_main D.R D.host p hp hs w' ho).2.2.2 P hP w hc).2.2 h),
        isConjPl_iff_conjPl.2 hc⟩
  · rintro (h | ⟨w', h, hc⟩)
    · exact overP_of_under hP (mem_aboveK.1 h)
    · exact ((splitsC_main D.R D.host p hp hs w' (overP_of_under hP (mem_aboveK.1 h))).2.2.2 P hP w
        (isConjPl_iff_conjPl.1 hc)).1

end One

end GlobalTheory.BigOn.Inhab

end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem shLift_const_mul {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (a : ℂ) (f : GL (Fin n) F → ℂ) (δ : GL (Fin n) F') :
    shLift s (fun x => a * f x) δ = a * shLift s f δ := by
  unfold shLift
  split_ifs <;> simp

theorem shLift_cusp_kills_J : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ n k : ℕ, 0 < n → Module.finrank F F' ∣ n → Reg (Nat.card F) n k →
    Kills (shLift s (cusp (pullθ ι θ) n k)) (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n) := by
  intro F F' _ _ _ _ s hl hs ι θ hθ n k hn hln hreg
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  haveI : Module.Finite F F' := Module.Finite.of_finite
  haveI : IsGalois F F' := inferInstance
  have hΓ : Nat.card (F' ≃ₐ[F] F') = Module.finrank F F' := IsGalois.card_aut_eq_finrank F F'
  haveI : Finite (F' ≃ₐ[F] F') := Nat.finite_of_card_ne_zero (by rw [hΓ]; exact hl.ne_zero)
  letI : Fintype (F' ≃ₐ[F] F') := Fintype.ofFinite _
  haveI : Fact (Nat.card (F' ≃ₐ[F] F')).Prime := ⟨hΓ ▸ hl⟩
  have hgen : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := by
    intro t
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (Subgroup.zpowers s) with h | h
    · exact absurd (Subgroup.zpowers_eq_bot.1 h) hs
    · rw [h]; exact Subgroup.mem_top t

  have hθ' : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → pullθ ι θ x = pullθ ι θ y → x = y := by
    intro x y hx hy hxy
    apply ι.toRingHom.injective
    exact hθ (ι x) (ι y) ((map_ne_zero ι.toRingHom).2 hx) ((map_ne_zero ι.toRingHom).2 hy) hxy
  set l := Module.finrank F F' with hldef
  set q := Nat.card F with hqdef
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hcardF' : Nat.card F' = q ^ l := Module.natCard_eq_pow_finrank

  obtain ⟨X, hX, hXg, hXs⟩ := GlobalTheory.T.exists_virtualCharacter_shintani_psi_lift F F' s hl hs ι θ hθ k n
  set c : ℂ := (-1) ^ (n - 1) with hc
  have hc2 : c = 1 ∨ c = -1 := neg_one_pow_eq_or ℂ (n - 1)
  set X' : GHat F F' n → ℂ := fun g => c * X g with hX'
  have hX'v : X' ∈ Virt ℂ ℂ (GHat F F' n) := by
    rcases hc2 with h | h
    · have : X' = X := by funext g; simp [hX', h]
      rw [this]; exact hX
    · have : X' = -X := by funext g; simp [hX', h]
      rw [this]; exact neg_mem hX
  have hcusp : cusp (pullθ ι θ) n k = fun x => c * psiG (rootSum (pullθ ι θ) k) n x := rfl
  have hX's : ∀ δ, X' (inl δ * inr s) = shLift s (cusp (pullθ ι θ) n k) δ := by
    intro δ
    rw [hcusp, shLift_const_mul, ← hXs δ]

  obtain ⟨hchar, hnorm⟩ := GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular F (pullθ ι θ) hθ' n k hn hreg
  have hclc : IsCl (cusp (pullθ ι θ) n k) := by
    intro x y
    rw [hcusp]
    simp only
    rw [((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 n (fun _ => 0) (fun _ => 0)).2.2 (rootSum (pullθ ι θ) k)).1 x y]
  have hiso := GlobalTheory.T.shintaniLiftClassFunction_isometry F F' s hgen n _ _ hclc hclc
  rw [hnorm] at hiso
  have hGne : (Nat.card (GL (Fin n) F) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := GL (Fin n) F)).ne'
  have hnorm' : ∑ᶠ δ, X' (inl δ * inr s) * star (X' (inl δ * inr s)) = (Nat.card (GL (Fin n) F') : ℂ) := by
    simp only [hX's]
    apply mul_left_cancel₀ hGne
    rw [hiso, mul_comm]

  obtain ⟨hdeg, hlift⟩ := GlobalTheory.T.deg_liftL_and_reg_pow q l [(n, k)] hq2 hl.pos (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨hn, hln, hreg⟩)
  have hdegn : deg (liftL q l [(n, k)]) = n := by rw [hdeg]; simp [deg]
  have hYchar : IsChar ℂ ℂ (J θ (liftL q l [(n, k)]) n) := by
    apply GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ _ _ n hdegn.symm
    intro p hp
    rw [hcardF']
    exact hlift p hp
  have hYst : ∀ g, J θ (liftL q l [(n, k)]) n (galAct F F' n s g) = J θ (liftL q l [(n, k)]) n g :=
    GlobalTheory.T.harishChandraProduct_shintaniLift_galois F F' θ s [(n, k)] n hdegn.symm

  obtain ⟨m, hm⟩ := hln
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hm; omega
    · exact h
  obtain ⟨z, hz, hzsum⟩ := GlobalTheory.T.cuspidal_galois_pairing_eq_pm_one_prime_degree F F' s hl hs ι θ hθ m k n hm0 hm hreg
  have hpair : ∑ᶠ g, X' (inl g) * star (J θ (liftL q l [(n, k)]) n g)
      = ((if c = 1 then z else -z : ℤ) : ℂ) * (Nat.card (GL (Fin n) F') : ℂ) := by
    have : (fun g : GL (Fin n) F' => X' (inl g) * star (J θ (liftL q l [(n, k)]) n g))
        = fun g => c * (X (inl g) * star (J θ (liftL q l [(n, k)]) n g)) := by
      funext g; simp only [hX']; ring
    rw [this, ← mul_finsum]
    simp only [hXg]
    rw [hzsum]
    rcases hc2 with h | h
    · rw [h]; simp
    · rw [h]; have : (-1 : ℂ) ≠ 1 := by norm_num
      simp [this]
  have hndvd : ¬ ((Nat.card (F' ≃ₐ[F] F') : ℤ) ∣ (if c = 1 then z else -z)) := by
    rw [hΓ]
    intro hd
    have hd' : (l : ℤ) ∣ z := by
      split_ifs at hd
      · exact hd
      · exact (dvd_neg).1 hd
    have h1 : (l : ℤ) ∣ 1 := by
      rcases hz with h | h
      · rwa [h] at hd'
      · rw [h] at hd'; exact (dvd_neg).1 hd'
    have : l ∣ 1 := by exact_mod_cast h1
    exact hl.one_lt.ne' (Nat.dvd_one.1 this)
  have hK := GlobalTheory.T.twisted_virtualCharacter_norm_one_support (GL (Fin n) F') (F' ≃ₐ[F] F') (galAct F F' n) s (hΓ ▸ hl) hs X' hX'v hnorm'
    (J θ (liftL q l [(n, k)]) n) hYchar hYst _ hpair hndvd
  have hfun : (fun δ => X' (inl δ * inr s)) = shLift s (cusp (pullθ ι θ) n k) := funext hX's
  rw [hfun] at hK
  exact hK

end GlobalTheory.Shin
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

private theorem eqv_of_isIso' (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ⟶ E') [IsIso f] : Eqv R f F := by
  intro n
  refine ⟨fun x y hxy => ?_, fun x => ⟨pull R (inv f) F n x, ?_⟩⟩
  · have hx := pull_comp R (inv f) f F n x
    have hy := pull_comp R (inv f) f F n y
    rw [IsIso.inv_hom_id, pull_id] at hx hy
    rw [hx, hy, hxy]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem contCone_bc_affine : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffineHom (G.obj i).hom) → ∀ (W : Scheme.{0}) (r : W ⟶ S), IsAffine W → ContCone R F ((bc (sch.map r)).mapCone c) := by
  intro R _ F hF S I _ _ G c hc hG W r hW
  haveI : IsConnected I := IsCofiltered.isConnected I
  obtain ⟨e, -⟩ := bc_sch_iso S W r
  let P : Over S ⥤ Scheme.{0} := Over.pullback r ⋙ Over.forget W
  have hlim : IsLimit (P.mapCone c) := isLimitOfPreserves P hc
  have haff : ∀ i, IsAffine ((G ⋙ P).obj i) := by
    intro i
    change IsAffine (pullback (G.obj i).hom r)
    haveI := hG i
    exact isAffine_of_isAffineHom (pullback.snd (G.obj i).hom r)
  have h1 : ContCone R F (sch.mapCone (P.mapCone c)) := GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit R F hF I (G ⋙ P) (P.mapCone c) hlim haff
  let α : (G ⋙ P) ⋙ sch ⟶ G ⋙ bc (sch.map r) :=
    { app := fun i => e.hom.app (G.obj i)
      naturality := fun i j f => e.hom.naturality (G.map f) }
  refine (ContCone.iff_of_eqv R F I _ _ (sch.mapCone (P.mapCone c)) ((bc (sch.map r)).mapCone c) α (e.hom.app c.pt)
    (fun i => e.hom.naturality (c.π.app i)) (fun i => eqv_of_isIso' R F _) (eqv_of_isIso' R F _)).1 h1

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem eqv_of_iso (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ≅ E') : Eqv R f.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R f.inv F n, fun x => ?_, fun y => ?_⟩
  · rw [← pull_comp, Iso.inv_hom_id, pull_id]
  · rw [← pull_comp, Iso.hom_inv_id, pull_id]

theorem contCone_of_represented : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (D : I ⥤ PSh) (c : Cone D), IsLimit c → (∀ i, ∃ Z : Scheme.{0}, IsAffine Z ∧ Nonempty (yoneda.obj Z ≅ D.obj i)) → (∃ Z : Scheme.{0}, Nonempty (yoneda.obj Z ≅ c.pt)) → ContCone R F (disc.mapCone c) := by
  intro R _ F hF I _ _ D c hc hD hpt
  choose Z hZ he using hD
  obtain ⟨Z0, ⟨e0⟩⟩ := hpt
  let e : ∀ i, yoneda.obj (Z i) ≅ D.obj i := fun i => (he i).some

  let G : I ⥤ Scheme.{0} :=
    { obj := Z
      map := fun {i j} f => yoneda.preimage ((e i).hom ≫ D.map f ≫ (e j).inv)
      map_id := fun i => yoneda.map_injective (by simp)
      map_comp := fun {i j k} f g => yoneda.map_injective (by simp) }
  let isoYD : G ⋙ yoneda ≅ D := NatIso.ofComponents e (fun {i j} f => by simp [G])

  let s : Cone G :=
    { pt := Z0
      π :=
        { app := fun i => yoneda.preimage (e0.hom ≫ c.π.app i ≫ (e i).inv)
          naturality := fun i j f => yoneda.map_injective (by simp [G]) } }
  have hs : IsLimit s := by
    apply isLimitOfReflects yoneda
    have h1 : IsLimit ((Cone.postcompose isoYD.inv).obj c) := (IsLimit.postcomposeInvEquiv isoYD c).symm hc
    refine h1.ofIsoLimit (Cone.ext e0.symm (fun i => ?_))
    simp [s]
    rfl
  have h0 : ContCone R F (sch.mapCone s) := GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit R F hF I G s hs hZ
  let αI : G ⋙ sch ≅ D ⋙ disc := (Functor.associator G yoneda disc).symm ≪≫ Functor.isoWhiskerRight isoYD disc
  let βI : sch.obj Z0 ≅ disc.obj c.pt := disc.mapIso e0
  refine (GlobalTheory.T.of_etaleCohomologyEquivalence_diagram R F I (G ⋙ sch) (D ⋙ disc) (sch.mapCone s) (disc.mapCone c) αI.hom βI.hom
    (fun i => ?_) (fun i => eqv_of_iso R F (αI.app i)) (eqv_of_iso R F βI)).mp h0
  simp only [Functor.mapCone_π_app, αI, βI, s, sch, Functor.comp_map]
  simp [isoYD, ← Functor.map_comp]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES


theorem _root_.GlobalTheory.T.integers_surjective_of_rank_one : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → Function.Surjective (algebraMap (𝓞 D.F) D.O) := by
  first | (exact @GlobalTheory.UPel.HT.Datum.algebraMap_surjective_of_m_eq_one) | (exact GlobalTheory.UPel.HT.Datum.algebraMap_surjective_of_m_eq_one) | (intros; apply GlobalTheory.UPel.HT.Datum.algebraMap_surjective_of_m_eq_one  <;> assumption)
end
