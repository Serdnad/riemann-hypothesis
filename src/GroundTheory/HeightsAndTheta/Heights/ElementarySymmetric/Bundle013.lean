module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LengthQuotientEqLengthH0
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechExact
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqCech
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PIdealTwistFamily
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotAdd
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrLenRestrict
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanish
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle026
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.RigSymFormTauINontrivial
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace RestrLenEuler

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem length_toNat_eq_finrank (M : Type w) [AddCommGroup M] [Module k M] :
    (Module.length k M).toNat = Module.finrank k M := by
  by_cases h : Module.Finite k M
  · rw [Module.length_eq_finrank]; rfl
  · rw [Module.finrank_of_not_finite h, Module.length_eq_rank]
    have : Cardinal.aleph0 ≤ Module.rank k M := by
      by_contra hlt
      exact h (Module.rank_lt_aleph0_iff.mp (not_le.mp hlt))
    rw [Cardinal.toENat_eq_top.mpr this]
    rfl

theorem vanish_of_fg (F : SubFamily k x Ω) (hF : ∀ I, (F.sub I).FG) :
    ∃ c₀ : ℤ, ∀ i : ℕ, 1 ≤ i → ∀ c : ℤ, c₀ ≤ c → Subsingleton ((F.toSubSystem.twist (twistSys k x c)).H i) := by
  obtain ⟨M, -, hM⟩ := Extension.full k Ω N x Ω F hF
  obtain ⟨c₀, hc₀⟩ := TildeVanish.proof SerreVanish.full k Ω N x Ω M
  have h0 : M.tildeSys 0 = F.toSubSystem := SubSystem.ext_sub fun I => hM I
  refine ⟨c₀, fun i hi c hc => ?_⟩
  rw [← h0, ← SurjectiveClosed.tildeSys_eq_twist]
  exact hc₀ i hi c hc

def incl (F₁ F₂ : SubSystem k x Ω) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I : Chart x) :
    F₂.sub I →ₗ[k] F₁.sub I where
  toFun y := ⟨y, h21 I y.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl



theorem quotH_subsingleton (F₁ F₂ : SubSystem k x Ω) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (i : ℕ)
    (h1 : Subsingleton (F₁.H i)) (h2 : Subsingleton (F₂.H (i + 1))) :
    Subsingleton (SubSystem.quotH F₁ F₂ i) := by
  have hdd := CechDSq.full (N + 1) (support x) k (fun I : Chart x => F₁.sub I) F₁.res
    (fun _ _ _ _ _ => LinearMap.ext fun _ => rfl)
  have L := Cech.longExact (R := k) (U := support x)
    (A := fun I : Chart x => F₂.sub I) (B := fun I : Chart x => F₁.sub I)
    (C := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
    (ρA := F₂.res) (ρB := F₁.res) (ρC := SubSystem.quotRes F₁ F₂)
    (dA := fun _ => ⊤) (dB := fun _ => ⊤) (dC := fun _ => ⊤)
    (φ := incl F₁ F₂ h21) (ψ := fun I => (SubSystem.quotSub F₁ F₂ I).mkQ)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => Submodule.mem_top)
    (fun _ _ _ => Submodule.mem_top)
    (fun I a b hab => Subtype.ext (show (a : Ω) = b from congrArg (fun z : F₁.sub I => (z : Ω)) hab))
    (fun I y => (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I)).mpr y.2)
    (fun I m _ hm => ⟨⟨m, (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I)).mp hm⟩, Submodule.mem_top, rfl⟩)
    (fun I z _ => (Submodule.Quotient.mk_surjective _ z).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
    (fun _ _ _ _ _ => Submodule.mem_top) hdd
  obtain ⟨-, hex⟩ := L
  obtain ⟨hg, δ, hgδ, -⟩ := hex i
  have hB : Subsingleton (Cech.Hdeg (fun I : Chart x => F₁.sub I) (fun _ => (⊤ : Submodule k _)) F₁.res i) :=
    haveI : Subsingleton (Cech.H (fun I : Chart x => F₁.sub I) F₁.res i) := h1
    (SnapperQuotientAdditivity.hdegTopEquiv _ _ i).toEquiv.subsingleton
  have hA : Subsingleton (Cech.Hdeg (fun I : Chart x => F₂.sub I) (fun _ => (⊤ : Submodule k _)) F₂.res (i + 1)) :=
    haveI : Subsingleton (Cech.H (fun I : Chart x => F₂.sub I) F₂.res (i + 1)) := h2
    (SnapperQuotientAdditivity.hdegTopEquiv _ _ (i + 1)).toEquiv.subsingleton
  have hC : Subsingleton (Cech.Hdeg (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
      (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₁ F₂) i) := by
    refine ⟨fun a b => ?_⟩
    have hz : ∀ y : Cech.Hdeg (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
        (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₁ F₂) i, y = 0 := by
      intro y
      obtain ⟨b, hb⟩ := (hgδ y).mp (Subsingleton.elim _ _)
      rw [← hb, Subsingleton.elim b 0, map_zero]
    rw [hz a, hz b]
  exact (SnapperQuotientAdditivity.hdegTopEquiv _ _ i).symm.toEquiv.subsingleton

end RestrLenEuler


open RestrLenEuler in
theorem RestrLenEuler.proof : RestrLenEuler.Statement.{u, w} := by
  intro k _ Ω _ _ N x qq hqq _ t L n
  set Ls : Fin t → SubSystem k x Ω := fun j => (L j).toSubSystem with hLs
  let Q : LineBundle k x := twistPowsBundle (twistBundle k x 0) t L n
  have hQ : Q.toSubSystem = (twistSys k x 0).twistPows t Ls n :=
    twistPowsBundle_toSubSystem (twistBundle k x 0) t L n
  obtain ⟨G, hG, hGfg⟩ := IdealTwistFamily.proof k Ω N x Q qq hqq
  obtain ⟨a₁, ha₁⟩ := vanish_of_fg Q.toSubFamily Q.fg
  obtain ⟨a₂, ha₂⟩ := vanish_of_fg G hGfg
  obtain ⟨a₃, ha₃⟩ := SurjectiveClosed.proof Extension.full IdealTwistFamily.proof
    (TildeVanish.proof SerreVanish.full) k Ω N x Q qq hqq
  refine Filter.eventually_atTop.mpr ⟨max a₁ (max a₂ a₃), fun c hc => ?_⟩
  have hc₁ : a₁ ≤ c := le_of_max_le_left hc
  have hc₂ : a₂ ≤ c := le_of_max_le_left (le_of_max_le_right hc)
  have hc₃ : a₃ ≤ c := le_of_max_le_right (le_of_max_le_right hc)
  set F₁ := ((twistSys k x 0).twistPows t Ls n).twist (twistSys k x c) with hF₁
  have hF₁Q : F₁ = Q.toSubSystem.twist (twistSys k x c) := by rw [hQ]
  have hF₂ : (((twistSys k x 0).twist (idealSys x qq)).twistPows t Ls n).twist (twistSys k x c) =
      F₁.twist (idealSys x qq) := by
    rw [twistPows_twist_comm, SurjectiveClosed.twist_twist_comm]
  have hF₂G : F₁.twist (idealSys x qq) = G.toSubSystem.twist (twistSys k x c) := by
    rw [hG, hF₁Q, SurjectiveClosed.twist_twist_comm]
  have h21 : ∀ I, (F₁.twist (idealSys x qq)).sub I ≤ F₁.sub I :=
    SurjectiveClosed.twist_idealSys_le F₁ qq
  have hvan : ∀ i, 1 ≤ i → Subsingleton (SubSystem.quotH F₁ (F₁.twist (idealSys x qq)) i) := by
    intro i hi
    refine quotH_subsingleton F₁ _ h21 i ?_ ?_
    · rw [hF₁Q]; exact ha₁ i hi c hc₁
    · rw [hF₂G]; exact ha₂ (i + 1) (by omega) c hc₂
  have hlift := ha₃ c hc₃
  rw [← hF₁Q] at hlift
  unfold pieceChar restrLen
  rw [hF₂, QuotientH0Length.length_secs_eq _ _ hlift, length_toNat_eq_finrank, eulerCharQuot,
    Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul]; rfl
  · intro i _ hi
    have := hvan i (Nat.one_le_iff_ne_zero.mpr hi)
    rw [Module.finrank_zero_of_subsingleton]
    simp
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) h

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

theorem serreVanishing_graded_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman.SerreVanish.Statement :=
  (GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.SerreVanish.equiv
    GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.proof).1
    GroundTheory.Heights₂.Heights.Kleiman.SerreVanish.full.{0, 0}

end

end GroundTheory.Heights₂.Heights.KeyFormula
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

theorem InterNumTie.proof (hRL : RestrLenRestrict.Statement.{u, w}) : InterNumTie.Statement.{u, w} := by
  intro k _ Ω _ _ N x e pp b hsub
  classical
  obtain ⟨j, hjp⟩ := hsub.relevant
  have hj : x j ≠ 0 := fun h0 => hjp (hsub.le ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0)))
  obtain ⟨hcp, hpt⟩ := PrimeFiltration.Point.full k Ω N x pp hsub.isPrime hsub.homog hsub.le j hj hjp
  have := hcp
  let A := chartRing k x (singleChart hj)
  let Ip : Ideal A := chartPrime pp hj
  let ψ : A →ₐ[k] Ip.ResidueField := IsScalarTower.toAlgHom k A Ip.ResidueField
  have hker : RingHom.ker ψ = Ip := Ideal.ker_algebraMap_residueField Ip
  let y : Fin (N + 1) → Ip.ResidueField := fun i => ψ (ratio hj i)
  have hxy : ∀ i, y i ≠ 0 → x i ≠ 0 := by
    intro i h hx
    apply h
    have h0 : ratio (S := k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])
    change ψ (ratio hj i) = 0
    rw [h0, map_zero]
  have hpy : primeOf (S := k) y = pp := hpt _ ψ hker
  have hxy' : primeOf (S := k) x ≤ primeOf (S := k) y := hpy ▸ hsub.le
  have hsubW : IsSubvar y pp e := ⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩
  have hyj : y j ≠ 0 := fun h0 => hjp (hpy ▸ (mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0))
  have hy0 : y ≠ 0 := fun h => hyj (congrFun h j)
  set I := pp.comap (oneBlock (S := k) (N := N)) with hI_def
  have hI : I = primeOfOne (S := k) y := by rw [primeOfOne, hpy]
  have hIp : NumbersDVR.IsMultiProjPrime I := hI ▸ isMultiProjPrime_primeOfOne y hy0
  have hIdim : FieldNumbers.relDim I = ((e : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, hI, HilbertPositive.ringKrullDim_primeOfOne, hpy,
      hsub.dim]
    simp
  let H : ℤ → ℤ := fun m => NumbersDVR.hilbFn I (fun _ : Unit => m)
  let R : ℤ → ℤ := fun m => restrLen pp (twistSys k x m)
  have hY : ∀ᶠ n : ℕ in atTop, restrLen pp (twistSys k y (n : ℤ)) = H n := by
    filter_upwards [TwistSections.full k _ N y hy0] with n hn
    rw [← hpy, SectionsOverLocalization.restrLen_primeOf_eq_finrank y hyj, hn, HilbertPositive.finrank_piece_eq_hilbFn, ← hI]
  obtain ⟨r₀, hr₀⟩ := RestrictTwist.full.1 k Ω N x _ y hxy hxy' 0
  have hXY := hRL k Ω N x _ y hxy hxy' pp e hsubW (twistBundle k x 0) (twistBundle k y 0) r₀ hr₀
  have hRH : ∀ᶠ n : ℕ in atTop, R n = H n := by
    filter_upwards [hY, hXY] with n h1 h2
    have e1 : (twistBundle k y 0).toSubSystem = twistSys k y 0 := rfl
    have e2 : (twistBundle k x 0).toSubSystem = twistSys k x 0 := rfl
    rw [e1, e2, twistSys_zero_twist, twistSys_zero_twist] at h2
    rw [← h1, h2]
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hRH
  have hRH' : ∀ m : ℤ, (n₀ : ℤ) ≤ m → R m = H m := by
    intro m hm
    have h := hn₀ m.toNat (by omega)
    rwa [Int.toNat_of_nonneg (by omega)] at h
  let bs : Fin e → Unit → ℤ := fun i _ => b i
  have hMD := (FieldNumbers.MixedDiffConst.full k Unit (fun _ => Fin (N + 1)) I hIp.multiHomog hIp.relevant e
    hIdim).1 bs
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp hMD
  set B : ℤ := ∑ i, b i with hB
  have hev : ∀ᶠ c : ℕ in atTop, interSum pp (fun i => twistSys k x (b i)) c = NumbersDVR.intNum k I bs := by
    filter_upwards [eventually_ge_atTop (m₀ () - B).toNat,
      eventually_all.mpr fun T : Finset (Fin e) => eventually_ge_atTop ((n₀ : ℤ) - ∑ i ∈ T, b i).toNat]
      with c hc1 hc2
    rw [SectionsOverLocalization.interSum_twistSys, ← hm₀ (fun _ => (c : ℤ) + B)
      (fun u => by cases u; change m₀ () ≤ (c : ℤ) + B; omega), SectionsOverLocalization.mixedDiff_eq_sum]
    refine Fintype.sum_bijective compl compl_involutive.bijective _ _ fun T => ?_
    have hsum : (∑ i ∈ Tᶜ, bs i) = fun _ : Unit => ∑ i ∈ Tᶜ, b i := by
      funext u
      rw [Finset.sum_apply]
    have hc : (n₀ : ℤ) ≤ ∑ i ∈ T, b i + c := by have := hc2 T; omega
    have hsplit := Finset.sum_add_sum_compl T b
    have hcard : Tᶜ.card = e - T.card := by rw [Finset.card_compl, Fintype.card_fin]
    rw [show restrLen pp (twistSys k x (∑ i ∈ T, b i + c)) = H (∑ i ∈ T, b i + c) from hRH' _ hc, hsum, hcard]
    change (-1) ^ (e - T.card) * H (∑ i ∈ T, b i + c) =
      (-1) ^ (e - T.card) * NumbersDVR.hilbFn I ((fun _ : Unit => (c : ℤ) + B) - fun _ => ∑ i ∈ Tᶜ, b i)
    have hfun : ((fun _ : Unit => (c : ℤ) + B) - fun _ => ∑ i ∈ Tᶜ, b i) =
        fun _ : Unit => ∑ i ∈ T, b i + c := by
      funext u
      simp only [Pi.sub_apply]
      omega
    rw [hfun]
  unfold interNum
  exact (tendsto_const_nhds.congr' (hev.mono fun c h => h.symm)).limUnder_eq

theorem InterNumTie.of_restrictQuot (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) :
    InterNumTie.Statement.{u, w} :=
  InterNumTie.proof (RestrLenRestrict.proof
    (SurjectiveClosed.proof Extension.full.{u, w, w} IdealTwistFamily.proof
      (TildeVanish.proof SerreVanish.full.{u, w})) hRQ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end
