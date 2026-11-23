module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1893
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2449
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2423
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle034
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle036
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle005
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem isKC_Eab_of_posC {p q : ℕ} {c d : Ix p q} (h : posC c d) : IsKC (Eab c d) := by
  intro a b hab
  have hcd : sameBlock c d := by
    cases c <;> cases d <;> simp_all [posC, sameBlock]
  simp only [Eab, Matrix.single_apply]
  split_ifs with h1
  · obtain ⟨rfl, rfl⟩ := h1
    exact absurd hcd hab
  · rfl

theorem sameBlock_refl {p q : ℕ} (a : Ix p q) : sameBlock a a := by
  cases a <;> trivial

theorem isKC_Eab_diag {p q : ℕ} (c : Ix p q) : IsKC (Eab c c) := by
  intro a b hab
  simp only [Eab, Matrix.single_apply]
  split_ifs with h1
  · rcases h1 with ⟨rfl, rfl⟩
    exact absurd (sameBlock_refl _) hab
  · rfl

theorem mem_hwSub_iff {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ c, act (Eab c c) v = ((μ c : ℚ) : ℂ) • v) ∧ ∀ c d, posC c d → act (Eab c d) v = 0 := by
  simp [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem hw_sup_le (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (hG : Good act) (N N' : Submodule ℂ V) (hN : KStable act N) (hN' : KStable act N') (μ : Ix p q → ℚ) :
    (N ⊔ N') ⊓ hwSub act μ ≤ (N ⊓ hwSub act μ) ⊔ (N' ⊓ hwSub act μ) := by
  intro v hv
  obtain ⟨hvs, hvh⟩ := Submodule.mem_inf.1 hv
  obtain ⟨n, hn, n', hn', rfl⟩ := Submodule.mem_sup.1 hvs
  rw [mem_hwSub_iff] at hvh
  obtain ⟨hw, hpos⟩ := hvh
  have hI : KStable act (N ⊓ N') := fun X hX w hw' =>
    Submodule.mem_inf.2 ⟨hN X hX w (Submodule.mem_inf.1 hw').1, hN' X hX w (Submodule.mem_inf.1 hw').2⟩
  have h1 : ∀ c, act (Eab c c) n - ((μ c : ℚ) : ℂ) • n ∈ N ⊓ N' := by
    intro c
    refine Submodule.mem_inf.2 ⟨N.sub_mem (hN _ (isKC_Eab_diag c) n hn) (N.smul_mem _ hn), ?_⟩
    have e : act (Eab c c) n - ((μ c : ℚ) : ℂ) • n = -(act (Eab c c) n' - ((μ c : ℚ) : ℂ) • n') := by
      have := hw c
      rw [map_add (f := _), smul_add] at this
      rw [neg_sub, sub_eq_sub_iff_add_eq_add, this, add_comm]
    rw [e]
    exact N'.neg_mem (N'.sub_mem (hN' _ (isKC_Eab_diag c) n' hn') (N'.smul_mem _ hn'))
  have h2 : ∀ c d, posC c d → act (Eab c d) n ∈ N ⊓ N' := by
    intro c d hcd
    refine Submodule.mem_inf.2 ⟨hN _ (isKC_Eab_of_posC hcd) n hn, ?_⟩
    have e : act (Eab c d) n = -(act (Eab c d) n') := by
      have := hpos c d hcd
      rw [map_add (f := _)] at this
      exact eq_neg_of_add_eq_zero_left this
    rw [e]
    exact N'.neg_mem (hN' _ (isKC_Eab_of_posC hcd) n' hn')
  obtain ⟨n1, hn1N, hn1h, hd⟩ := GlobalTheory.T.exists_highestWeight_lift_mod_stable_subspace p q V act hG (N ⊓ N') N hI hN μ n hn h1 h2
  have hdN' : n + n' - n1 ∈ N' := by
    have : n + n' - n1 = (n - n1) + n' := by abel
    rw [this]
    exact N'.add_mem (Submodule.mem_inf.1 hd).2 hn'
  have hvH : n + n' ∈ hwSub act μ := (mem_hwSub_iff act μ _).2 ⟨hw, hpos⟩
  have : n + n' = n1 + (n + n' - n1) := by abel
  rw [this]
  exact Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨hn1N, hn1h⟩)
    (Submodule.mem_inf.2 ⟨hdN', (hwSub act μ).sub_mem hvH hn1h⟩)

end GlobalTheory.HoweR
end

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.CxReg

open GlobalTheory.LKCx.Regroup

variable {p : ℕ} [Fact p.Prime]

theorem sep_of_regAf (G : HTGroup p) (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (f : G.GAf → ℂ)
    (hreg : ∀ g, f g ≠ 0 → RegAf G g) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (hsym : sh G β = β) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) :
    (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) := by
  rintro y h hne ⟨z, hz, hfix⟩
  exact GlobalTheory.LKCx.minpoly_of_regAf_of_fixL p G v hv β hsym hR x t hx y h ⟨z, hz⟩ hfix (hreg _ hne)

theorem finite_pts_reg (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1)
    (L : G.Level) (f : G.GAf → ℂ) (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f)
    (hreg : ∀ g, f g ≠ 0 → RegAf G g) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ)
    (hf' : IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f') (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (hsym : sh G β = β) (htr : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) :
    Set.Finite {q : Pts G v β x t hx L.K.toSubgroup K' | ∃ y : grp G β, FixL G v β y (Quot.out q).2.1 ∧
      f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) *
        f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) ≠ 0} := by
  have hsep := sep_of_regAf G v hv f hreg β x t hx hsym htr
  obtain ⟨Y, hY⟩ := Classical.axiomOfChoice
    (fun P => GlobalTheory.T.orbital_integral_test_function_first p G ha v hv L f hf K' f' hf' β x t hx hsep hsym htr P)
  refine ((GlobalTheory.T.orbital_term_real_trivialisation p G ha v hv L f hf K' f' hf' β x t hx hsym htr).biUnion
    (fun P _ => (Y P).finite_toSet.biUnion
      (fun y₀ _ => GlobalTheory.T.orbital_integral_test_function_second p G ha v hv L f hf K' f' hf' β x t hx hsep hsym htr y₀))).subset ?_
  rintro q ⟨y, hy, hne⟩
  obtain ⟨y₀, hy₀, γ, rfl⟩ := hY _ y rfl ⟨Quot.out q, hy, hne⟩
  simp only [Set.mem_iUnion]
  exact ⟨_, ⟨γ * y₀ * γ⁻¹, Quot.out q, rfl, hy, hne⟩, y₀, hy₀, γ, hy, hne⟩

theorem class_summand_eq_term_of_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g) → ∀ (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (r : grp G P.β), (r : G.Cˣ × ℚˣ) = (P.γ, P.c) → (if (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v P.β *ᵥ z)).re ∧ FixL G v P.β r z) then wt (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * pointSum ((toAfF G P.β x t hx).comp (Subgroup.centralizer {r}).subtype) ((toP1 G P.β).comp (Subgroup.centralizer {r}).subtype) (MonoidHom.id (Gr G 1)) Kf K' (toAfF G P.β x t hx r) (toP1 G P.β r) f f' else 0) = (if ∃ μ, P.Mark μ then wt P.pol * P.term Kf f 1 K' f' else 0) := by
  intro p _ G hG v hv wt Kf f K' f' hf hf' P x t hx r hr
  have hiff := fix_iff_mark G hG v hv P r hr
  by_cases hm : ∃ μ, P.Mark μ
  · rw [if_pos (hiff.2 hm), if_pos hm]
    obtain ⟨μ, hμ⟩ := hm
    have hpos := cent_sim_pos p G P μ hG hμ
    set e := centEquiv G P hpos r hr with he
    have h1 : (toAfF G P.β x t hx).comp (Subgroup.centralizer {r}).subtype =
        (P.toAf x t hx).comp e.toMonoidHom := by
      ext1 y; rfl
    have h2 : (toP1 G P.β).comp (Subgroup.centralizer {r}).subtype = (P.toQr 1 1).comp e.toMonoidHom := by
      ext1 y
      show inclG G 1 (locC G y.1.1) = (MulAut.conj (1 : Gr G 1)⁻¹) (inclG G 1 (locC G y.1.1))
      simp
    have h3 : toAfF G P.β x t hx r = P.toAf x t hx P.self := by
      obtain ⟨r, hr'⟩ := r
      simp only at hr
      subst hr
      rfl
    have h4 : toP1 G P.β r = inclG G 1 P.atP := by
      show inclG G 1 (locC G (r : G.Cˣ × ℚˣ)) = _
      rw [hr]; rfl
    have h5 : minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P.pol := by
      rw [hr]; rfl
    rw [h1, h2, h3, h4, h5, GlobalTheory.pointSum_comp_mulEquiv, GlobalTheory.T.orbital_term_point_sum p G P Kf f K' f' hf hf' x t hx]
  · rw [if_neg (fun h => hm (hiff.1 h)), if_neg hm]

end GlobalTheory.LKCx.CxReg

namespace GlobalTheory.LKCx

end GlobalTheory.LKCx
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.finite_doubleCoset_rational_productOfLocalLevels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n)))) := by
  first | exact @GlobalTheory.BCT.finite_doubleCoset_globLev | exact GlobalTheory.BCT.finite_doubleCoset_globLev | (intros; apply GlobalTheory.BCT.finite_doubleCoset_globLev <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU (E := E) (n := n))), IsOpen (L : Set (finU (E := E) (n := n))) → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (L : Set (finU (E := E) (n := n)))) := by
  intro E _ _ _ n L hL
  exact GlobalTheory.BCT.ClassFinLev.finite_doubleCoset_of_isOpen L hL
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum.JetsUb

open GlobalTheory.AllWt GlobalTheory.CompHS

theorem floorGaps_sub_le {N : ℕ} (a : ℕ) (m : ℤ) (v : Fin N → ℤ) (hv : Antitone v) {i j : Fin N} (hij : i ≤ j) :
    floorGaps a m v i - floorGaps a m v j ≤ v i - v j := by
  have hij' : (i : ℕ) ≤ j := hij
  have e1 : floorGaps a m v i - floorGaps a m v j = ∑ k ∈ Finset.Ico (i : ℕ) j, gap v k / m := by
    simp only [floorGaps, ofGaps]
    rw [← Finset.sum_range_add_sum_Ico _ hij']
    ring
  have e2 : v i - v j = ∑ k ∈ Finset.Ico (i : ℕ) j, gap v k := by
    have h1 := ofGaps_gap v i i
    have h2 := ofGaps_gap v i j
    simp only [ofGaps] at h1 h2
    rw [← Finset.sum_range_add_sum_Ico _ hij'] at h2
    linarith
  rw [e1, e2]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_Ico.1 hk
  have hN : k + 1 < N := by have := j.2; omega
  have h0 : 0 ≤ gap v k := by
    rw [gap, dite_eq_left hN]
    have := hv (show (⟨k, by omega⟩ : Fin N) ≤ ⟨k + 1, hN⟩ from Fin.mk_le_mk.2 (by omega))
    omega
  exact Int.ediv_le_self _ h0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem thA_ub_le (P : WtPar Dw) (n : ℕ) (hp : 0 < Dw.p) (hu : ∀ τ, Antitone (P.u₁ τ)) (x : (E →+* ℂ) × ℕ) :
    thA Dw P.ub n x ≤ thA Dw P.u₁ n x := by
  have hd : ∀ τ (i j : Fin (Dw.p + Dw.q)), i ≤ j → P.ub τ i - P.ub τ j ≤ P.u₁ τ i - P.u₁ τ j :=
    fun τ i j h => floorGaps_sub_le _ _ _ (hu τ) h
  show (thExpZ Dw P.ub n x).toNat ≤ (thExpZ Dw P.u₁ n x).toNat
  apply Int.toNat_le_toNat
  obtain ⟨σ, i⟩ := x
  rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
  · by_cases hi : i < Dw.p
    · rw [thExpZ_big _ n τ i hi, thExpZ_big _ n τ i hi]
      have := hd τ ⟨i, by omega⟩ ⟨Dw.p - 1, by omega⟩ (Fin.mk_le_mk.2 (by omega))
      omega
    · rw [thExpZ_big_ge _ n τ i (by omega), thExpZ_big_ge _ n τ i (by omega)]
  · by_cases hi : i < Dw.q
    · rw [thExpZ_small _ n hp τ i hi, thExpZ_small _ n hp τ i hi]
      have := hd τ ⟨Dw.p - 1, by omega⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ (Fin.mk_le_mk.2 (by omega))
      omega
    · rw [thExpZ_small_ge _ n τ i (by omega), thExpZ_small_ge _ n τ i (by omega)]

theorem DF_ub_le (P : WtPar Dw) (n : ℕ) (hp : 0 < Dw.p) (hu : ∀ τ, Antitone (P.u₁ τ)) :
    Formalism.L2.Pj.DF Dw (thA Dw P.ub n) ≤ Formalism.L2.Pj.DF Dw (thA Dw P.u₁ n) := by
  unfold Formalism.L2.Pj.DF
  exact Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => thA_ub_le P n hp hu (τ, i)

end GlobalTheory.RefSum.JetsUb

theorem GlobalTheory.RefSum.JetNum.of_le {D : Formalism.BasicNotions.D7} {d d' : ℕ} {c : ℝ} (h : GlobalTheory.RefSum.JetNum D d c) (hd : d' ≤ d) :
    GlobalTheory.RefSum.JetNum D d' c := fun k => by
  obtain ⟨h1, h2, h3⟩ := h k
  have hd' : (d' : ℝ) ≤ d := by exact_mod_cast hd
  have hr : 0 ≤ GlobalTheory.PtTie.rr0 D := by unfold GlobalTheory.PtTie.rr0; positivity
  refine ⟨by omega, ?_, le_trans ?_ h3⟩
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hd' (by positivity)) h2
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : (d' : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd' 2
    linarith
end
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.CcEx

noncomputable section

open GlobalTheory.ClsVal.Cmp

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}

def anFibBas {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]
    {X : Data E r} {bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw}
    {x : Frame X.Ψ r} {L : Lt E r} {y : FrPt Xo c ℂ} (h : ∀ z w, hx X bas' idx x z w = hx X bas idx x z w)
    (A : AnFib X bas idx e x L y) : AnFib X bas' idx e x L y where
  ex := A.ex
  ex_add := A.ex_add
  ex_onto := A.ex_onto
  ex_ker := A.ex_ker
  ex_lin := A.ex_lin
  hol := A.hol
  der := A.der
  fr := A.fr
  fr_hol := A.fr_hol
  fr_ne := A.fr_ne
  fr_g := A.fr_g
  fr_0 := A.fr_0
  χ := A.χ
  χ_norm := A.χ_norm
  fr_per v hv j z hz := by rw [h, h]; exact A.fr_per v hv j z hz

theorem coord_eq {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas)
    {x : Frame X.Ψ r} (hx' : x ∈ X.dom) {p q : X.Ψ × Fin r} (h : ∀ v, per X x v p = per X x v q) : p = q := by
  obtain ⟨i, rfl⟩ := idx.surjective p
  obtain ⟨j, rfl⟩ := idx.surjective q
  have hsp := ((hx_laws E r X g bas idx 0 hs Even.zero x hx').2.2.2.2.2.2.1 ⊤ (by simp)).1
  have key : ∀ z : Fin g → ℂ, z i = z j := by
    intro z
    have hz : z ∈ Submodule.span ℝ (pv X idx x '' ((⊤ : Lt E r) : Set (Fin r → E))) := hsp ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨v, -, rfl⟩ := hz; exact h v
    | zero => rfl
    | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb]
    | smul a b _ hb => simp only [Pi.smul_apply, hb]
  by_contra hne
  have hij : j ≠ i := fun e => hne (by rw [e])
  have := key (Pi.single i 1)
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hij] at this
  exact one_ne_zero this

variable {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

theorem genReads_change (U : Unf Xo c σ r) (k : U.Comp) {g g' : ℕ}
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx' : Fin g' ≃ (U.X k).Ψ × Fin r) (e' : Fin g' ≃ Lt1 Dw)
    (hs : IsSympl (U.X k) bas) (hs' : IsSympl (U.X k) bas') (hi : IdxIs c σ (U.X k) idx e) (hi' : IdxIs c σ (U.X k) idx' e')
    (x : (U.X k).dom) (hon : IsONFr (U.X k) x.1) (ϑ' : (Fin g' → ℂ) → ℂ) (h : GenReads U k bas' idx' e' x ϑ') :
    ∃ ϑ, GenReads U k bas idx e x ϑ ∧ ∀ u : (U.X k).Ψ × Fin r → ℂ, ϑ' (u ∘ idx') = ϑ (u ∘ idx) ∧
      hx (U.X k) bas' idx' x.1 (u ∘ idx') (u ∘ idx') = hx (U.X k) bas idx x.1 (u ∘ idx) (u ∘ idx) := by
  have hg : g' = g := by simpa using Fintype.card_congr (idx'.trans idx.symm)
  subst hg
  obtain ⟨π, rfl⟩ : ∃ π : Equiv.Perm (Fin g'), e' = π.trans e := ⟨e'.trans e.symm, by ext1; simp⟩
  have hidx : idx' = π.trans idx := by
    ext1 j
    exact coord_eq idx hs x.2 fun v => (hi'.1 x.1 v j).trans (hi.1 x.1 v (π j)).symm
  subst hidx
  let _ : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨A, hA⟩ := h
  have hb : ∀ z w, hx (U.X k) bas idx x.1 z w = hx (U.X k) bas' idx x.1 z w := fun z w => by
    rw [(hx_of_isONFr E r g' 0 _ bas idx hs Even.zero _ hon).2.2, (hx_of_isONFr E r g' 0 _ bas' idx hs' Even.zero _ hon).2.2]
  refine ⟨ϑ' ∘ ren π, ⟨anFibBas hb (anFibRen π A), fun j z pt h1 h2 h3 => hA j (ren π z) pt h1 h2 h3⟩, fun u => ⟨rfl, ?_⟩⟩
  rw [hb]
  exact hx_ren _ bas' idx π x.1 (u ∘ idx) (u ∘ idx)

end Gen

theorem thA_smul' {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (a : ℂ) (φ : TF n g) (x : Frame X.Ψ r)
    (z : Fin n → Fin g → ℂ) : thA X bas idx (a • φ) x z = a * thA X bas idx φ x z := by
  simp only [thA, SW.thS, show ∀ y, (a • φ) y = a * φ y from fun _ => rfl, _root_.mul_assoc, tsum_mul_left]
  ring

theorem exists_ccIs_of_pair (hci : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {V W : HSp D} {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hP : IsPair ψ θ V W χV χW om) {mu : GA D W → ℂ} (hmu : MuVal W χV mu) (hmuQ : ∀ γ ∈ GQ W, ∀ h, mu (γ * h) = mu h)
    {r : ℕ} (hr : W.rank = r) {H : Geo.Tor.Host D.host.E} (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ)
    (hU : IsUnf U) (hr1 : 1 ≤ r) (hA : l.A = 1) {a : (D.host.E →+* ℂ) × ℕ → ℕ} (hdom : Dom a V.rank)
    {ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)}
    (hV0 : V.rank ≠ 0) (h1 : (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V) (h2 : (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W)
    (h3 : IsSelfDualC V ΛV) (h4 : IsSelfDualC W ΛW)
    (h5 : (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hmod : ∀ k, IsMod W hr (U.X k)) (hon : ∀ k, IsONFr (U.X k) (fun τ => x₀ τ.1))
    (hinv : ∀ k, IsInvOf W hr (U.X k) (fun τ => x₀ τ.1) s) {f : WO V W → ℂ}
    (hf : IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f)
    (dict : GA D W → Σ k, Frame (U.X k).Ψ r) : ∃ cc, CcIs θ V W hr U dict mu x₀ om f cc := by
  have hU' : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj U) := hU
  obtain ⟨Wt⟩ := nonempty_uw hU'
  have hw : IsIntegral ℤ (H.w0 : D.host.E) := H.w0.isIntegral_coe
  have hw' : (H.w0 : D.host.E) + cc (H.w0 : D.host.E) = 1 := by
    rw [cc, ← H.bar_eq]
    exact_mod_cast congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  have key : ∀ k : U.Comp, ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ (h : GA D W) (x : (U.X k).dom), latR hr (latG W h) = (U.X k).Λ →
      x.1 = frMove θ W hr (U.X k) h (fun τ => x₀ τ.1) → ∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ)
      (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X k) bas → IdxIs c σ (U.X k) idx e →
      ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads U k bas idx e x ϑ → ∀ w : WO V W, w.map (finPart D) = 0 →
        om (1, h) f w = a * mu h *
          cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx (U.X k) bas idx x.1
            (zOf θ V W hr (U.X k) idx x.1 w b) (zOf θ V W hr (U.X k) idx x.1 w b)) *
          ∏ b, ϑ (zOf θ V W hr (U.X k) idx x.1 w b) := by
    intro k
    have hsd : SelfD (U.X k) (U.X k).Λ := (uw_lattice _ H Dw l Xo c σ _ _ hσ hU' hr1 Wt k).2.1
    obtain ⟨Dc, -, -⟩ := exists_dic _ H Dw l c σ _ Wt.g V.rank (U.X k) a Wt.e hσ hU.1 (hU.2.1 k).1 (hU.2.1 k).2 hsd hdom
    have hi : IdxIs c σ (U.X k) Dc.idx Dc.e := ⟨Dc.per_eq, Dc.ty_eq⟩
    obtain ⟨v, hv⟩ := (TensVac.vacua _ _ _ _ Dc.bas Dc.idx V.rank Dc.sympl hP.even _ hw hw' _ hsd 1 _
      (Base.stdL_mem_Vset V.rank 1)).1
    obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.pow_generator_eq_const_mul_vacuum_theta hci _ H Dw l Xo c σ r U hσ hU hr1 hA k V.rank _ Dc.bas Dc.idx Dc.e hP.even
      Dc.sympl hi v hv
    obtain ⟨κ, -, hκ, hrd⟩ := GlobalTheory.T.exists_vacuum_multiplier_constant_per_lattice D ψ θ V W χV χW om hP mu hmu r _ hr (U.X k) Dc.bas Dc.idx (hmod k) Dc.sympl H hrt
      ΛV ΛW hV0 h1 h2 h3 h4 h5 hsd _ s (hon k) (hinv k) f hf v hv
    refine ⟨κ / C, ?_, fun h x hL hxe g bas idx e hs hie ϑ' hϑ' w hw0 => ?_⟩
    · obtain ⟨hd, hu, -⟩ := hx_of_isONFr _ r _ 0 _ Dc.bas Dc.idx Dc.sympl Even.zero _ (hon k)
      obtain ⟨⟨ϑ, hϑ⟩, hall⟩ := hC ⟨_, hd⟩ hu
      obtain ⟨t1, t2, t3⟩ := hall ϑ hϑ
      rw [norm_div, ← hκ _ hd hu ϑ C t1 t2 t3, div_self (norm_ne_zero_iff.2 hC0)]
    · obtain ⟨hon', -, hread⟩ := hrd h hL
      rw [← hxe] at hon' hread
      obtain ⟨-, hu, -⟩ := hx_of_isONFr _ r _ 0 _ Dc.bas Dc.idx Dc.sympl Even.zero _ hon'
      obtain ⟨ϑ, hϑ, hch⟩ := genReads_change U k Dc.bas Dc.idx Dc.e bas idx e Dc.sympl hs hi hie x hon' ϑ' hϑ'
      have t3 := ((hC x hu).2 ϑ hϑ).2.2 (zOf θ V W hr (U.X k) Dc.idx x.1 w)
      have e1 : ∏ b, ϑ' (zOf θ V W hr (U.X k) idx x.1 w b) = ∏ b, ϑ (zOf θ V W hr (U.X k) Dc.idx x.1 w b) :=
        Finset.prod_congr rfl fun b _ => (hch _).1
      have e2 : ∑ b, hx (U.X k) bas idx x.1 (zOf θ V W hr (U.X k) idx x.1 w b) (zOf θ V W hr (U.X k) idx x.1 w b) =
          ∑ b, hx (U.X k) Dc.bas Dc.idx x.1 (zOf θ V W hr (U.X k) Dc.idx x.1 w b)
            (zOf θ V W hr (U.X k) Dc.idx x.1 w b) :=
        Finset.sum_congr rfl fun b _ => (hch _).2
      rw [hread w hw0, e1, e2, t3, thA_smul']
      field_simp
  choose cc hcc hkey using key
  refine ⟨cc, hcc, fun h γ hat hx' g bas idx e hs hi ϑ hϑ w hw0 => ?_⟩
  rw [← hmuQ γ hat.1 h]
  exact hkey _ (γ * h) ⟨_, hx'⟩ hat.2.1 hat.2.2 g bas idx e hs hi ϑ hϑ w hw0

end

end GlobalTheory.AdTh.CcEx
end

section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.cuspFormGrowth_le_imageDegree_lowerWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ (Z : Comp Xo c) (G G' : WTZ E), Even G.2 → Even G'.2 → growthOn U Z G ≠ ⊤ → BirOn U Z G → ValMult U Z G G' → growthOn U Z G' ≤ (compDeg U Z G : ℝ≥0∞) := by
  first | exact @GlobalTheory.DegVal.growthOn_le_compDeg | exact GlobalTheory.DegVal.growthOn_le_compDeg | (intros; apply GlobalTheory.DegVal.growthOn_le_compDeg <;> assumption)
end
