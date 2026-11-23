module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyCoeffsInSubalgebra
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.KrullDimLtOfNotLeTriangular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PointEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ThickOf
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
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

theorem UpperTheory.V.Pr.exists_nice_prime_above_of_large_dim :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (C₀ n : ℕ), F.Ok C₀ → F.Big C₀ → (n = 2 ∨ n = 3) → ∀ (S : UpperTheory.V.Fr.Space O F n) (x : Ideal S.A) (L : S.Loc x), ¬ S.u.triP ≤ x → ∀ I : Ideal S.B, S.FinLam I → ∀ P : Ideal L.R, I ≤ L.π P → ((n * F.d + 1 : ℕ) : WithBot ℕ∞) ≤ UpperTheory.V.Pr.qdim P → ∃ p, UpperTheory.V.Pr.Nice L.ρ p ∧ P ≤ p := by
  intro l _ O _ _ _ _ F C₀ n hOk hBig hn S x L hx I hI P hIP hdim
  haveI := L.co
  haveI : IsLocalHom (algebraMap L.O' L.R) := L.co.isLocalHom
  haveI : CharP (IsLocalRing.ResidueField O) l := UpperTheory.V.Fr.IsCoef.char (O := O)
  obtain ⟨_, hP⟩ := UpperTheory.V.Fr.l51 hOk hn S x L hx
  obtain ⟨hM, hC⟩ := UpperTheory.V.Fr.krull_dim_lt_of_not_le_triangular hOk hn S x L hBig hx
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {w} := hw.maximalIdeal_eq
  have hwO' : algebraMap O L.O' w ∈ IsLocalRing.maximalIdeal L.O' := by
    rw [← L.unr]
    exact Ideal.mem_map_of_mem _ (hmax ▸ Ideal.subset_span rfl)
  have hwR : algebraMap O L.R w ∈ IsLocalRing.maximalIdeal L.R := by
    rw [IsScalarTower.algebraMap_apply O L.O' L.R]
    exact map_nonunit (algebraMap L.O' L.R) _ hwO'
  let a : Option (F.V × Fin n × Fin n) → Ideal L.R := fun o =>
    match o with
    | none => L.ρ.triM
    | some (v, i, j) =>
      if i = j then ⊤ else
        Ideal.map L.b I ⊔ Ideal.map (algebraMap O L.R) (IsLocalRing.maximalIdeal O) ⊔
          Ideal.span {y | ∃ g ∈ F.Nv v, y = ↑((L.ρ.ψ v i) g) - ↑((L.ρ.ψ v j) g)}
  have hN : 1 ≤ n * F.d := by
    have h1 : 1 ≤ n := by rcases hn with h | h <;> omega
    have h2 : 1 ≤ F.d := by have := hBig.1; omega
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have ha : ∀ o, UpperTheory.V.Pr.qdim (a o) < ↑(n * F.d) := by
    intro o
    rcases o with _ | ⟨v, i, j⟩
    · exact hM
    · by_cases hij : i = j
      · simp only [a, hij, if_true]
        show ringKrullDim (L.R ⧸ (⊤ : Ideal L.R)) < _
        rw [ringKrullDim_eq_bot_of_subsingleton]
        exact WithBot.bot_lt_coe _
      · simp only [a, hij, if_false]
        exact hC I hI v i j hij
  obtain ⟨p, hp, hPp, hp1, hwp, hnot⟩ :=
    UpperTheory.V.Pr.nicePrimeEx L.R (algebraMap O L.R w) hwR (n * F.d) hN _ a ha P hdim
  have hmap : Ideal.map (algebraMap O L.R) (IsLocalRing.maximalIdeal O) ≤ p := by
    rw [hmax, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact hwp
  refine ⟨p, ⟨hp, hp1, ?_, ⟨?_, ?_⟩, ?_⟩, hPp⟩
  · have hl : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      exact CharP.cast_eq_zero _ l
    have := hmap (Ideal.mem_map_of_mem (algebraMap O L.R) hl)
    simpa using this
  · intro h
    rw [hP, top_le_iff] at h
    exact hp.ne_top h
  · exact hnot none
  · intro v i j hij hco
    apply hnot (some (v, i, j))
    simp only [a, hij, if_false]
    refine sup_le (sup_le ?_ hmap) ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro y hy
      exact hPp (hIP hy)
    · rw [Ideal.span_le]
      rintro y ⟨g, hg, rfl⟩
      exact hco g hg
end

section

theorem UpperTheory.V.Pr.p1Of :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n), T.FirstPrimeConditionTransfer := by
  intro l _ O _ _ _ _ _ F n T Φ hΦ h4 J hJ x L p hp hTI hM P hP hPp
  have key : ∀ Q : Ideal L.R, J.map Φ ≤ L.π Q ↔ J ≤ Q.comap (T.phi Φ L : T.B.B →+* L.R) := by
    intro Q
    rw [Ideal.map_le_iff_le_comap]
    exact Iff.rfl
  obtain ⟨y, j, hker, hloc, hρ, hψ, hpt⟩ :=
    UpperTheory.V.Pr.pointEx l O F n T Φ hΦ x L p hp.prime hp.dim hp.char
  subst hker
  obtain ⟨h1, h3, hI, -⟩ := UpperTheory.V.Pr.niceOf l O F n T x L y j hloc hp hρ hψ
  rw [key] at hM ⊢
  haveI := hP
  exact hJ y (j.comp (T.phi Φ L)) ⟨h1, hI hTI, h3, h4 y⟩ hpt (fun a ha => hM ha) (T.back Φ L P)
    (fun a ha => hPp ha)
end

section

private theorem chain_nat {α : Type} {r : α → α → Prop} {p q : α} (H : Relation.ReflTransGen r p q) :
    ∃ (h : ℕ) (c : ℕ → α), c 0 = p ∧ c h = q ∧ ∀ i < h, r (c i) (c (i + 1)) := by
  induction H with
  | refl => exact ⟨0, fun _ => p, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | @tail b d _ hbd ih =>
    obtain ⟨h, c, h0, hh, hs⟩ := ih
    refine ⟨h + 1, fun i => if i ≤ h then c i else d, ?_, ?_, ?_⟩
    · simp [h0]
    · simp
    · intro i hi
      by_cases hih : i < h
      · have h1 : i ≤ h := le_of_lt hih
        have h2 : i + 1 ≤ h := hih
        simp only [h1, h2, if_true]
        exact hs i hih
      · have hie : i = h := by omega
        subst hie
        simp only [le_refl, if_true, show ¬ (i + 1 ≤ i) from by omega, if_false, hh]
        exact hbd

theorem UpperTheory.V.Pr.rankThree_deformationSetup_splitting_condition :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (T : UpperTheory.V.Pr.Setup F 3), T.SecondThirdPrimeConditionTransfer := by
  intro l _ O _ _ _ _ _ F T Φ hΦ hN4 J hJ x L p q hp hTE hch hPex P' hP' hP'q hP'TI
  haveI := L.co
  obtain ⟨P, hP, hPp, hPTI, hJP⟩ := hPex
  obtain ⟨h, c, hc0, hch', hs⟩ := chain_nat hch
  have back_le : ∀ (A : Ideal L.R) [A.IsPrime] (w : UpperTheory.V.W.Point T.r)
      (k : L.R →ₐ[O] w.A), A ≤ RingHom.ker k →
      (T.back Φ L A).asIdeal ≤ RingHom.ker (k.comp (T.phi Φ L)) := by
    intro A _ w k hA z hz
    have h2 : (T.phi Φ L) z ∈ RingHom.ker k := hA hz
    rw [RingHom.mem_ker] at h2 ⊢
    exact h2
  have hN : ∀ i, i ≤ h → UpperTheory.V.Pr.Nice L.ρ (c i) ∧ L.ρ.TE (c i) := by
    intro i hi
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact ⟨(hs i hlt).1, (hs i hlt).2.1⟩
    · rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0
        rw [hc0]
        exact ⟨hp, hTE⟩
      · have hl := hs (i - 1) (by omega)
        rw [show i - 1 + 1 = i by omega] at hl
        exact ⟨hl.2.2.1, hl.2.2.2.1⟩
  have hpt : ∀ i : Fin (h + 1), ∃ (w : UpperTheory.V.W.Point T.r) (k : L.R →ₐ[O] w.A),
      RingHom.ker k = c i ∧ IsLocalHom k ∧
      UpperTheory.V.W.mat w.ρ = T.K.tw (UpperTheory.V.Fr.NRep.map (↑k) L.ρ) ∧
      w.ψ = T.K.twψ (UpperTheory.V.Fr.NRep.map (↑k) L.ρ) ∧ T.B.IsPt w (k.comp (T.phi Φ L)) := by
    intro i
    have hi := (hN i (Nat.lt_succ_iff.mp i.isLt)).1
    exact UpperTheory.V.Pr.pointEx l O F 3 T Φ hΦ x L (c i) hi.prime hi.dim hi.char
  choose y j hker hloc hmat hψ hIsPt using hpt
  have hNE : ∀ i, (y i).NiceE := by
    intro i
    have hi := hN i (Nat.lt_succ_iff.mp i.isLt)
    have hn : UpperTheory.V.Pr.Nice L.ρ (RingHom.ker (j i)) := by rw [hker]; exact hi.1
    have ht : L.ρ.TE (RingHom.ker (j i)) := by rw [hker]; exact hi.2
    obtain ⟨h1, h3, _, hE⟩ := UpperTheory.V.Pr.niceOf l O F 3 T x L (y i) (j i) (hloc i) hn (hmat i) (hψ i)
    exact ⟨h1, hE ht, h3, hN4 (y i)⟩
  have hlink : ∀ i : Fin h, ∃ E : Ideal L.R, E.IsPrime ∧ UpperTheory.V.Fr.Thick L.ρ E ∧ E ≤ c i ∧ E ≤ c (i + 1) :=
    fun i => (hs i i.isLt).2.2.2.2
  choose E hEp hEt hE1 hE2 using hlink
  let e : Fin h → PrimeSpectrum T.B.B := fun i => @UpperTheory.V.Pr.Setup.back _ _ _ _ _ _ _ _ _ _ T Φ _ L (E i) (hEp i)
  have key := hJ h y (fun i => (j i).comp (T.phi Φ L)) e hNE hIsPt (by
      intro i
      haveI := hEp i
      refine ⟨UpperTheory.V.Pr.thickOf l O F T Φ hΦ x L (E i) (hEt i), ?_, ?_⟩
      · apply back_le
        rw [hker]
        simpa using hE1 i
      · apply back_le
        rw [hker]
        simpa using hE2 i)
    (by
      haveI := hP
      refine ⟨T.back Φ L P, UpperTheory.V.Pr.stableOf l O F 3 T Φ hΦ x L P hPTI, ?_, ?_⟩
      · intro z hz
        exact (Ideal.map_le_iff_le_comap.mp hJP) hz
      · apply back_le
        rw [hker]
        simpa [hc0] using hPp)
  haveI := hP'
  have hfin := key (T.back Φ L P') (by
      apply back_le
      rw [hker]
      simpa [hch'] using hP'q)
    (Or.inl (UpperTheory.V.Pr.stableOf l O F 3 T Φ hΦ x L P' hP'TI))
  rw [Ideal.map_le_iff_le_comap]
  intro z hz
  exact hfin hz
end
