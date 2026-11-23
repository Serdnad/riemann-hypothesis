module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCharactersAgreeCommonStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle141
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle219
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle181
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairSplitTermNearReferenceBySkew
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle161
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle218
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle222
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle187
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle206
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle220
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle221
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle013
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver GlobalTheory.HL
open scoped Classical

namespace GlobalTheory.RelGPoint

open GlobalTheory.HL.CoordExist

theorem exists_coord_of_point {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) (hM : M.OK) {V : Type}
    [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r)
    (hrk : Module.finrank E V = k + 2 * r + 1) (hpt : P.IsPoint) (hN : P.NormsOK) (hG : P.Gv ≠ 0) :
    ∃ S : Frames M.L r k, Nonempty (Coord P S) := by
  obtain ⟨w, hw⟩ := hpt
  obtain ⟨hTo, hT, hTo', hT', hgg⟩ := hN
  have := hM.loc
  have := nontriv M.L
  have := H.free
  have := H.fin
  let b := Module.finBasisOfFinrankEq E V hrk
  obtain ⟨ϖ, hϖ, hϖg⟩ : ∃ ϖ : 𝒪[F], Irreducible ϖ ∧ ∀ g, M.split = some g → ϖ = g.q := by
    rcases h : M.split with _ | g
    · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
      exact ⟨ϖ, hϖ, fun g hg => by cases hg⟩
    · exact ⟨g.q, g.q_irr, fun g' hg => by cases hg; rfl⟩
  refine ⟨
    { ϖ := ϖ
      ϖ_irr := hϖ
      Hm := Matrix.of fun i j => H.h (b i) (b j)
      herm := hermND H b
      T := Units.mk0 _ hT
      T' := Units.mk0 _ hT'
      f := fun a => b.equivFun (P.A.f a)
      f' := fun a => b.equivFun (P.B.f a)
      es := fun a => b.equivFun (P.A.es a)
      es' := fun a => b.equivFun (P.B.es a)
      gram := fun a c => by rw [hf_basis]; exact gram_eq _ _ _
      gram' := fun a c => by rw [hf_basis]; exact gram_eq _ _ _
      dual := fun a c => by rw [hf_basis]; exact dual_eq _ _ _
      dual' := fun a c => by rw [hf_basis]; exact dual_eq _ _ _
      iso := fun a c => by rw [hf_basis]; exact P.A.h_ss _ _
      iso' := fun a c => by rw [hf_basis]; exact P.B.h_ss _ _
      w := w
      relevant := fun a c => ?_
      G_ne := ?_
      gg := M.split.isSome
      gg_ok := fun h => ?_ }, ⟨
    { e := b.equivFun
      h_eq := fun x y => hf_basis H b x y
      f_eq := fun _ => rfl
      f'_eq := fun _ => rfl
      es_eq := fun _ => rfl
      es'_eq := fun _ => rfl
      T_eq := rfl
      T'_eq := rfl
      gg_none := fun h => by simp only [h, Option.isSome_none]
      gg_some := fun g h => ⟨by simp only [h, Option.isSome_some], hϖg g h⟩ }⟩⟩
  · rw [hf_basis, ← hw, mul_right_comm, ← mul_pow]
    simp [HermSp.Zhat]
  · simp only [hf_basis]
    have h1 : H.Dl P.A.f P.B.f (r + 1) =
        lead (Matrix.of fun a c => H.h (P.B.f c) (P.A.f a)) (Fin.last (r + 1)) := by
      unfold HermSp.Dl; rw [dite_eq_left le_rfl]; rfl
    have h2 : H.Dl P.A.f P.B.f r =
        lead (Matrix.of fun a c => H.h (P.B.f c) (P.A.f a)) (Fin.last r).castSucc := by
      unfold HermSp.Dl; rw [dite_eq_left (Nat.le_succ r)]; rfl
    rw [← h1, ← h2]
    exact hG
  · obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨⟨u, v, hu, hv⟩, -⟩ := hgg g hg
    exact ⟨not_field M.L g, unit_of hTo u hu, unit_of hTo' v hv⟩

theorem relG_of_point : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.IsPoint → P.NormsOK → P.Gv ≠ 0 → P.RelG (theta M) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hpt hN hG
  obtain ⟨S, ⟨c⟩⟩ := exists_coord_of_point M hM H r k P hrk hpt hN hG
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨hli, -, -, hD, hDl, -⟩ := GlobalTheory.FrameBasic.main M.L r k S
  obtain ⟨-, -, -, hSt, hpsi, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hZm : S.Zh = H.Zhat P.A.f P.B.f := by
    ext a b
    show S.h (S.f' b) (S.f a) = H.h (P.B.f b) (P.A.f a)
    rw [c.f_eq, c.f'_eq, c.h_eq]
  have hDm : ∀ l (hl : l ≤ r + 1), P.Dm l = S.D ⟨l, Nat.lt_succ_of_le hl⟩ := by
    intro l hl
    unfold FPair.Dm HermSp.Dl
    rw [dite_eq_left hl]
    unfold Frames.D lead
    rw [hZm]
  have hmap : ∀ (f : Fin (r + 1) → V) (g : Fin (r + 1) → S.V), (∀ a, g a = c.e (f a)) →
      ∀ x ∈ H.Xp f, c.e x ∈ Submodule.span E (Set.range g) := by
    intro f g hg x hx
    have hgf : g = (c.e : V →ₗ[E] S.V) ∘ f := funext hg
    rw [hgf, Set.range_comp, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hx
  have hdisj := (linearIndependent_sum.1 hli).2.2
  refine ⟨?_, ?_, hG, ?_, ?_, hpt, hN⟩
  · rw [eq_bot_iff]
    intro x hx
    have h0 : c.e x = 0 :=
      (Submodule.disjoint_def.1 hdisj) _ (hmap _ _ c.f_eq x hx.1) (hmap _ _ c.f'_eq x hx.2)
    rw [Submodule.mem_bot]
    exact c.e.map_eq_zero_iff.1 h0
  · rw [hDm (r + 1) le_rfl]
    exact hD
  · intro l hl
    rw [hDm l hl]
    by_cases h : S.D ⟨l, Nat.lt_succ_of_le hl⟩ = 0
    · exact Or.inl h
    · exact Or.inr (hDl _ h)
  · intro g hg
    rw [(hpsi g).1, (hpsi g).2]
    exact GlobalTheory.HL.CharAgree.psi_eq_psi' M.L r k S _ ((hSt g).1 hg)

end GlobalTheory.RelGPoint
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem inMir_diag1_succ {g : ℕ} [Fact g.Prime] {k : ℕ} (h : Gn g k) :
    InMir ((diag1 h (k + 1) : Gn g (k + 1)) : Mt g (k + 1)) := by
  unfold InMir diag1 toG
  intro i j hi
  split_ifs with hu
  · have hk : ¬ ((i : ℕ) < k) := by omega
    refine (congrFun (congrFun hu.unit_spec i) j).trans ?_
    simp [hk]
  · rfl

theorem mirClass_diag1_eq_sum : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (k : ℕ) (F : Gn g (k + 1) → ℂ), IsMirClass F → ∀ h : Gn g k, F (diag1 h (k + 1)) = ∑ i ∈ Finset.range (k + 1), hc i (k - i) (der ψ i F) (gg ψ (k - i)) k h := by
  intro g inst ψ hψ k F hF h
  rw [GlobalTheory.T.mirabolicConjInvariant_eq_sum_induced_derivatives g ψ hψ (k + 1) F (by omega) hF (diag1 h (k + 1)) (inMir_diag1_succ h)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact GlobalTheory.T.mirabolicInduction_blockDiag_eq_harishChandra_gelfandGraev g ψ i k (der ψ i F) hik (GlobalTheory.T.isClassFunction_bernsteinZelevinskyDerivative g ψ i (k + 1) F (by omega) hF) h

end GlobalTheory.GLm
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.pairs_isometry_no_fixed_vector_count_bound : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), 1 ≤ x → 1 ≤ x' → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (((x : ℝ) * x') ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (cf K + 3 * (2 * j + 1)) * ((2 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x') ^ (Module.finrank K V)) := by
  first | exact @GlobalTheory.PairNoFix.main | exact GlobalTheory.PairNoFix.main | (intros; apply GlobalTheory.PairNoFix.main <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.stabilizer_hermitianLattice_of_deep_star_congruence : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → ∀ s ∈ N.Rs, (∀ x ∈ N.P0, s x - x ∈ 𝔠 ^ (3 * e + 10) • N.P0) → s • Λ = Λ := by
  first | exact @GlobalTheory.DegCnt.stab_of_deep_congruence | exact GlobalTheory.DegCnt.stab_of_deep_congruence | (intros; apply GlobalTheory.DegCnt.stab_of_deep_congruence <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePair_split_term_near_reference_by_skew : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → N.Split Λ → ∀ e : ℕ, 2 ≤ e → 𝔠 ^ e • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')) ≤ Λ → 𝔠 ^ e • (Λ ⊓ rs (𝓞 K) (N.F.Xa N.j)) ≤ N.P0 → 𝔠 ^ e • (Λ ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ≤ N.P0 → Λ ⊓ rs (𝓞 K) (II N.F N.F') ≤ N.P0 → ∃ s ∈ N.ZI, N.Near (𝔠 ^ (6 * e + 30)) (s • Λ) := by
  first | exact @GlobalTheory.DegCnt.DualPos.near_of_skew | exact GlobalTheory.DegCnt.DualPos.near_of_skew | (intros; apply GlobalTheory.DegCnt.DualPos.near_of_skew <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem gaugeSubEx_mem_maxK_iff {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) :
    g ∈ maxK ε ↔ g ∈ Formalism.REAL.KG ε := by
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  constructor
  · intro h
    have h1 : (uMat g)ᴴ * uMat g = 1 := h
    have h2 : uMat g * (uMat g)ᴴ = 1 := mul_eq_one_comm.mp h1
    refine ⟨Matrix.mem_unitaryGroup_iff'.mpr h1, ?_⟩
    show uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g
    calc uMat g * Formalism.REAL.Jm ε = uMat g * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by rw [hg]
      _ = (uMat g * (uMat g)ᴴ) * Formalism.REAL.Jm ε * uMat g := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.one_mul]
  · intro h
    exact Matrix.mem_unitaryGroup_iff'.mp h.1

theorem gaugeSubEx_haarK (n : ℕ) (ε : Fin n → Bool) :
    ∃ μ : Measure (Formalism.REAL.UJ ε), μ (maxK ε)ᶜ = 0 ∧ μ Set.univ = 1 ∧
      ∀ k ∈ maxK ε, μ.map (fun g => k * g) = μ := by
  have hK : maxK ε = (Formalism.REAL.KG ε : Set (Formalism.REAL.UJ ε)) :=
    Set.ext fun g => gaugeSubEx_mem_maxK_iff ε g
  have hc : IsCompact (Formalism.REAL.KG ε : Set (Formalism.REAL.UJ ε)) :=
    isCompact_iff_compactSpace.mpr (Formalism.REAL.instCompactKG n ε)
  have hm : MeasurableSet (maxK ε) := hK ▸ hc.isClosed.measurableSet
  have hv : Measurable (Subtype.val : Formalism.REAL.KG ε → Formalism.REAL.UJ ε) := measurable_subtype_coe
  have := Formalism.REAL.compact_haar_probability n ε
  refine ⟨(Formalism.REAL.muK ε).map Subtype.val, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hv hm.compl]
    have : (Subtype.val : Formalism.REAL.KG ε → Formalism.REAL.UJ ε) ⁻¹' (maxK ε)ᶜ = ∅ := by
      ext k
      simp [hK]
    rw [this, measure_empty]
  · rw [Measure.map_apply hv MeasurableSet.univ, Set.preimage_univ, measure_univ]
  · intro k hk
    have hk' : k ∈ Formalism.REAL.KG ε := (gaugeSubEx_mem_maxK_iff ε k).mp hk
    have h := map_mul_left_eq_self (Formalism.REAL.muK ε) ⟨k, hk'⟩
    rw [Measure.map_map (measurable_const_mul k) hv]
    conv_rhs => rw [← h]
    rw [Measure.map_map hv (measurable_const_mul _)]
    rfl

theorem gaugeSubEx : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, 1 ≤ j i) → IsIsoFlag ε j W → (∃ μ, SigmaFinite μ ∧ IsGaugeSub (flagN ε W) (dimN n j) μ) ∧ (∃ μ, SigmaFinite μ ∧ IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μ) ∧ ∃ μ : Measure (Formalism.REAL.UJ ε), μ (maxK ε)ᶜ = 0 ∧ μ Set.univ = 1 ∧ ∀ k ∈ maxK ε, μ.map (fun g => k * g) = μ := by
  intro n ε a j W _ hW
  refine ⟨?_, ?_, gaugeSubEx_haarK n ε⟩
  · obtain ⟨A, E, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_nilpotentAlgebra_isotropicFlagUnipotentRadical n ε a j W hW
    rw [h4]
    exact GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra n ε A _ E h1 h2 h3
  · obtain ⟨A, E, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_algebra_isotropicFlagSelfAdjointLevi n ε a j W hW
    rw [h4]
    exact GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra n ε A _ E h1 h2 h3

end GlobalTheory.FlagMeas
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.offBlock_entries_bounded_normalForm_pairOfFlags : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De R₀ : ℝ), TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (y : UToff β → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg k r z' (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) ≤ R₀ → Sg k r z (g₀ * (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → ∀ p, ‖y p‖ ≤ R₀ ^ (2 * r) * De := by
  first | exact @GlobalTheory.Amp.NfOff.offBlock_le | exact GlobalTheory.Amp.NfOff.offBlock_le | (intros; apply GlobalTheory.Amp.NfOff.offBlock_le <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.FlagPieces

theorem sizesLe_stepLe (I : AutInst) (x : I.GA) {t : ℝ} (ht : 0 < t)
    (A' : Submodule (𝓞 I.E) (Fin I.n → I.E)) : SizesLe I x (stepLe I x t) A' t := by
  intro N _ hN hne
  have hle : stepLe I x t ≤ lamX I x := GlobalTheory.PointFlag.stepLe_le I x t
  have hne0 : stepLe I x t ≠ ⊥ := by
    intro h0
    apply hne
    rw [h0] at hN ⊢
    exact le_bot_iff.mp hN.1
  exact (GlobalTheory.PointFlag.sizeQ_le I x hle hN hne).trans ((GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t ht).2.2.2.2.1 hne0)

theorem perpIn_bot (I : AutInst) (x : I.GA) : perpIn I x ⊥ = lamX I x := by
  apply le_antisymm
  · exact Submodule.span_le.mpr fun y hy => hy.1
  · intro y hy
    apply Submodule.subset_span
    refine ⟨hy, fun s hs => ?_⟩
    rw [(Submodule.mem_bot _).mp hs]
    simp [Formalism.UG.hform]

theorem flag_pieces : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ → (∀ i, SatX I x (S i) ∧ SatX I x (perpIn I x (S i)) ∧ S i ≤ perpIn I x (S (Fin.last a)) ∧ perpIn I x (S (Fin.last a)) ≤ perpIn I x (S i) ∧ rkK (perpIn I x (S i)) + rkK (S i) = I.n) ∧ perpIn I x (S 0) = lamX I x ∧ SizesLe I x (perpIn I x (S (Fin.last a))) (S (Fin.last a)) 2 ∧ ∀ i : Fin a, SizesGe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (perpIn I x (S i.castSucc)) (perpIn I x (S i.succ)) (τ i)⁻¹ ∧ S i.succ ≠ ⊥ ∧ largestSize (bas I) (frm I x) (S i.succ) ≤ τ i ∧ SizesGe I x (lamX I x) (S i.succ) (if h : (i : ℕ) + 1 < a then τ ⟨i + 1, h⟩ else 1 / 2) := by
  intro I x a S τ hF
  have h35 := GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I x
  have h34 := (GlobalTheory.T.canonicalFlag_exists_unique_semistable I x).2.2 a S τ hF
  have hsat : ∀ m, SatX I x (S m) := fun m => GlobalTheory.PointFlag.flag_sat hF m
  have hperpLast : perpIn I x (S (Fin.last a)) = stepLe I x 2 := by
    rw [hF.2.2.1, (h35.2.2.1 (1 / 2) (by norm_num)).2]
    norm_num
  have hle_last : ∀ i, S i ≤ S (Fin.last a) := fun i => hF.2.1.monotone (Fin.le_last i)
  have hlast_le : S (Fin.last a) ≤ stepLe I x 2 := by
    rw [hF.2.2.1]
    exact (GlobalTheory.PointFlag.stepLt_le_stepLe I x _).trans (GlobalTheory.PointFlag.stepLe_mono I x (by norm_num))
  refine ⟨fun i => ?_, ?_, ?_, fun i => ?_⟩
  · have hp := h35.2.2.2 (S i) (S i) (hsat i) (hsat i) le_rfl
    have hp' := h35.2.2.2 (S i) (S (Fin.last a)) (hsat i) (hsat _) (hle_last i)
    refine ⟨hsat i, hp.1, ?_, hp'.2.2.2.1, hp.2.1⟩
    rw [hperpLast]
    exact (hle_last i).trans hlast_le
  · rw [hF.1]
    exact GlobalTheory.FlagPieces.perpIn_bot I x
  · rw [hperpLast]
    exact GlobalTheory.FlagPieces.sizesLe_stepLe I x (by norm_num) _
  · obtain ⟨hcs, _, hlarge, hge, hlei⟩ := h34.1 i
    obtain ⟨hτpos, _, hsucc, _⟩ := hF.2.2.2.2.1 i
    have hsuccle : S i.succ ≤ lamX I x := by
      rw [hsucc]
      exact GlobalTheory.PointFlag.stepLe_le I x _
    refine ⟨?_, hlei, ?_, ?_, hlarge.le, ?_⟩
    · intro N hlt hle
      exact hge N hlt (hle.trans hsuccle)
    · rw [hcs, hsucc, (h35.2.2.1 _ hτpos).1, (h35.2.2.1 _ hτpos).2]
      exact GlobalTheory.FlagPieces.sizesLe_stepLe I x (inv_pos.mpr hτpos) _
    · intro h
      have hlt : S i.castSucc < S i.succ := hF.2.1 (Fin.castSucc_lt_succ ..)
      rw [h] at hlt
      exact not_lt_bot hlt
    · split_ifs with h
      · have e : (⟨(i : ℕ) + 1, h⟩ : Fin a).castSucc = i.succ := Fin.ext (by simp)
        have hn := (h34.1 ⟨(i : ℕ) + 1, h⟩).2.2.2.1
        rw [e] at hn
        intro N hlt hle
        exact hn N hlt hle
      · have hi := i.isLt
        have e : i.succ = Fin.last a := Fin.ext (by simp; omega)
        rw [e, hF.2.2.1]
        intro N hlt hle
        exact (GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.1 N hlt hle

end GlobalTheory.FlagPieces
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.majorantLengthTailBound_of_moments : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r)) (Φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) (q : ℕ) (H₁ : ℝ), inWb k r z → 0 < H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → (∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lA k r z (Matrix.of x) a)⁻¹ ^ (2 * q)) * (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ) → TailBd z νS Φ q H₁ := by
  first | exact @GlobalTheory.Amp.TailTwo.tailBd_of_moments | exact GlobalTheory.Amp.TailTwo.tailBd_of_moments | (intros; apply GlobalTheory.Amp.TailTwo.tailBd_of_moments <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.exists_rational_flag_block_fixing_lattice : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ γ : ∀ i, GL (Fin (j i)) I.E, (∀ i y, (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ y ∈ Λ i ↔ y ∈ Λ i) → ∀ g₀ ∈ latGroup I₀ x₀, ∃ g ∈ latGroup I xf, ∃ (Γ : Matrix (Fin I.n) (Fin I.n) I.E) (γ₀ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E), (∀ v, uMat (g v) = (I.P v)⁻¹ * Γ.map (I.φ v) * I.P v) ∧ (∀ v, uMat (g₀ v) = (I₀.P v)⁻¹ * γ₀.map (I₀.φ v) * I₀.P v) ∧ (∀ i, Γ * T i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)) ∧ Γ * T₀ = T₀ * γ₀.map e := by
  first | exact @GlobalTheory.LeviRat.exists_rat_block | exact GlobalTheory.LeviRat.exists_rat_block | (intros; apply GlobalTheory.LeviRat.exists_rat_block <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_closedEmbedding_orthogonalUnitary_realPlace : ∀ (n m : ℕ) (ε : Fin n → Bool) (ε' : Fin m → Bool) (s : Bool) (x₀ : Fin n → ℂ) (B : Matrix (Fin n) (Fin m) ℂ), m + 1 = n → qEps ε x₀ = sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → ∃ j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε, Topology.IsClosedEmbedding j ∧ ∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g := by
  first | exact @GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal | exact GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal | (intros; apply GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.measurable_flagGramNumberNormalized_indicator : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → γ ∈ GG k r → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => Yj k r hj z z' γ (Matrix.of x)) ∧ ∀ R₀ y : ℝ, MeasurableSet (Eset0 k r hj z z' γ R₀ y) := by
  first | exact @GlobalTheory.Amp.YMeas.yj_measurable | exact GlobalTheory.Amp.YMeas.yj_measurable | (intros; apply GlobalTheory.Amp.YMeas.yj_measurable <;> assumption)
end
