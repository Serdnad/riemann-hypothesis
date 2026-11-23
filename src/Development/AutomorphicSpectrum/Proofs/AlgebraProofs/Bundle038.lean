module

import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.CharacterDataBaseChange
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderLatticeBase
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.Bundle002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle033
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle009
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.Bundle007
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem locFree_map_equiv (R : Subalgebra o Ω) {E E' : Type} [AddCommGroup E] [Module Ω E]
    [AddCommGroup E'] [Module Ω E'] (e : E ≃ₗ[Ω] E') {r : ℕ} {L : AddSubgroup E}
    (h : LocFree R r L) : LocFree R r (L.map e.toLinearMap.toAddMonoidHom) := by
  obtain ⟨hst, k, f, c, hf, hc, hs, hl⟩ := h
  refine ⟨?_, k, f, c, hf, hc, hs, fun l => ?_⟩
  · rintro a ha _ ⟨x, hx, rfl⟩
    exact ⟨a • x, hst a ha x hx, by simp⟩
  · obtain ⟨b, hb, hsp, hiff⟩ := hl l
    refine ⟨fun q => e (b q), hb.map' e.toLinearMap (LinearEquiv.ker e), ?_, fun v => ?_⟩
    · have : Set.range (fun q => e (b q)) = e.toLinearMap '' Set.range b := by
        rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, hsp, Submodule.map_top, LinearMap.range_eq_top]
      exact e.surjective
    · have key : ∀ n : ℕ, f l ^ n • v ∈ L.map e.toLinearMap.toAddMonoidHom ↔
          f l ^ n • e.symm v ∈ L := by
        intro n
        constructor
        · rintro ⟨x, hx, hxe⟩
          have : x = f l ^ n • e.symm v := by
            apply e.injective
            rw [map_smul, e.apply_symm_apply]
            exact hxe
          rwa [← this]
        · intro hx
          exact ⟨_, hx, by simp⟩
      simp only [key]
      rw [hiff (e.symm v)]
      constructor
      · rintro ⟨a, ha, hv⟩
        refine ⟨a, ha, ?_⟩
        have := congrArg e hv

        simpa [map_sum] using this
      · rintro ⟨a, ha, hv⟩
        refine ⟨a, ha, ?_⟩
        rw [hv]

        simp [map_sum]

theorem mem_stdLat (R : Subalgebra o Ω) {ι : Type} {v : ι → Ω} :
    v ∈ stdLat R ι ↔ ∀ j, v j ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem locFree_stdLat (R : Subalgebra o Ω) (m : ℕ) : LocFree R m (stdLat R (Fin m)) := by
  apply PositivityTheory.Xgn.LocallyFreeLatticeSpans.locFree_std <;> assumption

theorem locFree_divLat (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] {c : Ω}
    (hc : c ≠ 0) {r : ℕ} {L : AddSubgroup E} (h : LocFree R r L) : LocFree R r (divLat c L) := by
  have := locFree_map_equiv R (LinearEquiv.smulOfNeZero Ω E c⁻¹ (inv_ne_zero hc)) h
  convert this using 1
  ext v
  constructor
  · intro hv
    exact ⟨c • v, hv, by simp [smul_smul, hc]⟩
  · rintro ⟨x, hx, rfl⟩
    show c • (c⁻¹ • x) ∈ L
    simpa [smul_smul, hc] using hx

theorem locFree_map_mkQ_iff (R : Subalgebra o Ω) {E E₂ : Type} [AddCommGroup E] [Module Ω E]
    [AddCommGroup E₂] [Module Ω E₂] (q : E →ₗ[Ω] E₂) (hq : Function.Surjective q) {r : ℕ}
    (L : AddSubgroup E) :
    LocFree R r (L.map (LinearMap.ker q).mkQ.toAddMonoidHom) ↔ LocFree R r (L.map q.toAddMonoidHom) := by
  let e := q.quotKerEquivOfSurjective hq
  have h1 : (L.map (LinearMap.ker q).mkQ.toAddMonoidHom).map e.toLinearMap.toAddMonoidHom =
      L.map q.toAddMonoidHom := by
    rw [AddSubgroup.map_map]
    congr 1
  constructor
  · intro h
    rw [← h1]
    exact locFree_map_equiv R e h
  · intro h
    have h2 : (L.map q.toAddMonoidHom).map e.symm.toLinearMap.toAddMonoidHom =
        L.map (LinearMap.ker q).mkQ.toAddMonoidHom := by
      rw [← h1, AddSubgroup.map_map]
      ext v
      simp
    rw [← h2]
    exact locFree_map_equiv R e.symm h

theorem isBaseChange_bcMap (Ω C : Type) [Field Ω] [Field C] [Algebra Ω C] (ι : Type) [Finite ι] :
    IsBaseChange C (bcMap Ω C ι) := by
  have := Fintype.ofFinite ι
  have h := IsBaseChange.pi (S := C) (fun _ : ι => Algebra.linearMap Ω C)
    (fun _ => IsBaseChange.linearMap Ω C)
  exact h

theorem span_bcMap_annSub (Ω C : Type) [Field Ω] [Field C] [Algebra Ω C] (n i : ℕ) :
    Submodule.span C (bcMap Ω C (Fin n) '' (annSub Ω n i : Set (Fin n → Ω))) = annSub C n i := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    simp only [annSub, SetLike.mem_coe, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot] at hv ⊢
    intro j hj
    simp [bcMap, hv j hj]
  · intro v hv
    simp only [annSub, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot] at hv
    have : v = ∑ j, v j • bcMap Ω C (Fin n) (if (j : ℕ) < i then 0 else Pi.single j 1) := by
      ext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single k]
      · by_cases hk : (k : ℕ) < i
        · simp [hk, hv k hk, bcMap]
        · simp [hk, bcMap]
      · intro j _ hjk
        by_cases hj : (j : ℕ) < i
        · simp [hj, bcMap]
        · simp [hj, bcMap, Pi.single_apply, hjk.symm]
      · simp
    rw [this]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    simp only [annSub, SetLike.mem_coe, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot]
    intro k hk
    by_cases hj : (j : ℕ) < i
    · simp [hj]
    · have : k ≠ j := by rintro rfl; exact hj hk
      simp [hj, Pi.single_apply, this]

theorem spanOver_swap {C V Z Vc Zc : Type} [Field C] [Algebra o C] (RC : Subalgebra o C)
    [AddCommGroup V] [AddCommGroup Z] [AddCommGroup Vc] [AddCommGroup Zc]
    [Module C Vc] [Module C Zc] (b : V → Vc) (b' : Z → Zc) (Γ : AddSubgroup (Z × V)) :
    spanOver RC (Prod.map b b' '' (Γ.map (AddEquiv.prodComm (M := Z) (N := V)).toAddMonoidHom : AddSubgroup (V × Z))) =
      (spanOver RC (Prod.map b' b '' Γ)).map (AddEquiv.prodComm (M := Zc) (N := Vc)).toAddMonoidHom := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, _, ⟨_, ⟨⟨z, v⟩, hzv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a • (b' z, b v), ⟨a, ha, _, ⟨(z, v), hzv, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, ha, _, ⟨⟨z, v⟩, hzv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, _, ⟨_, ⟨(z, v), hzv, rfl⟩, rfl⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness
end
end

section

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

theorem _root_.GlobalTheory.T.hopf_order_lattice_base : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] [IsAlgClosed C] [CharZero C] (RC : Subalgebra o C) (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → ∀ (p : ℕ) [Fact p.Prime], v (p : C) < 1 → ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (φ : Equiv.Perm Sg), D.Base RC p w → ∀ AA : HopfOrder (C := C) RC (Fin n → F), AA.carrier.toAddSubgroup = D.M → FStable F AA.carrier → ∀ (σ : MulChar F RC), IsFund p σ → FlagConcl v p AA.carrier (Pi.basisFun F (Fin n)) σ → ∀ e : Sg → ℕ, (∀ τ a, χ τ a = ((σ ^ p ^ e τ) a : RC)) → (∀ τ, σ ^ p ^ e (φ τ) = σ ^ p ^ (e τ + 1)) → (∀ τ, (∀ g ∈ sqIdeal (augIdeal AA.carrier), (g, 0) ∈ D.Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ D.Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ D.Th τ) ∧ ∀ g ∈ eig AA.carrier (σ ^ p ^ e τ), (g, 0) ∈ D.Th τ → g ∈ sqIdeal (augIdeal AA.carrier)) → ∀ τ (i : Fin n), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) = D.kk τ i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk | exact GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_stdLat_iff_algebra (R : Subalgebra o Ω) {ι : Type} (v : ι → Ω) :
    v ∈ stdLat R ι ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem linMap_mem_stdLat {F : Type} [Zero F] [Fintype F] {n : ℕ} (R : Subalgebra o Ω) (χ : F → Ω)
    (hχ : ∀ a, χ a ∈ R) (v : Fin n → Ω) (hv : v ∈ stdLat R (Fin n)) :
    linMap n χ v ∈ stdLat R (Fin n → F) := by
  rw [mem_stdLat_iff_algebra] at hv ⊢
  intro x
  simp only [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hv i) (hχ _)

theorem hodge_annihilator_lattice {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F]
    [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω)
    (p : ℕ) (w : Ω) (χ : Sg → F → Ω) (hC : CharData R p w χ) (hB : D.Base R p w) (hp : p.Prime)
    (hN : IsNoetherianRing R) (hF : IsFractionRing R Ω) (hI : IsIntegrallyClosedIn R Ω)
    (φ : Equiv.Perm Sg) (hT : D.TestFacts R p w χ φ) (hG : D.Good₁ R p χ) (τ : Sg) :
    mulLat w (stdLat R _) ≤ D.af R p (χ τ) := by
  have H := GlobalTheory.T.lattice_good_base_change D R p w χ hC hB hG
  obtain ⟨hp0, hwR, -, -, hχ⟩ := hC
  intro x hx
  obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.mp hx
  have hu' : ∀ i, u i ∈ R := (mem_stdLat_iff_algebra R u).mp hu
  refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI n (D.af R p (χ τ)) (H.1 τ).1 _ ⟨1, ?_⟩ ?_
  · have hy : linMap n (χ τ) (w • u) ∈ stdLat R (Fin n → F) :=
      linMap_mem_stdLat R (χ τ) (hχ τ).2.2 _ ((mem_stdLat_iff_algebra R _).mpr fun i => by
        simpa using R.mul_mem hwR (hu' i))
    rw [LieLatticeData.af, AddSubgroup.mem_comap]
    refine AddSubgroup.mem_sup_right (AddSubgroup.mem_map.mpr ⟨_, hy, ?_⟩)
    simp [map_smul]
  · intro C _ _ _ _ RC hTP
    have hRC : ∀ a ∈ R, algebraMap Ω C a ∈ RC := hTP.2.2.2
    rw [← ((H.2 C RC hRC).2 τ).1]
    have hFa := hT C RC hTP
    refine hFa.le_af τ (AddSubgroup.mem_map.mpr ⟨bcMap Ω C (Fin n) u, ?_, ?_⟩)
    · exact (mem_stdLat_iff_algebra RC _).mpr fun i => by simpa [bcMap] using hRC _ (hu' i)
    · ext i
      simp [bcMap]

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsion_points_homomorphism_compatible : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∀ K : AddSubgroup N, (∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ G), z ≫ j = 1 ↔ ∃ φ : (T.A ⧸ vanIdeal T pt K) →ₐ[R] S, spMap φ ≫ (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) = z) → ∀ jN : N →+ N', (∀ x, pt' (jN x) = pt x ≫ j) → jN.ker = K ∧ ∀ g ∈ torsFun C T pt, (∀ k ∈ jN.ker, g k = 0) → g ∈ (augIdeal (torsFun C T' pt')).map (LinearMap.funLeft R C (jN : N → N')) * torsFun C T pt := by
  first | exact @GlobalTheory.CompanionTheory.Relay.torsion_points_homomorphism_compatible | exact GlobalTheory.CompanionTheory.Relay.torsion_points_homomorphism_compatible | (intros; apply GlobalTheory.CompanionTheory.Relay.torsion_points_homomorphism_compatible <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsion_points_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → (∃ AA : HopfOrder (C := C) R N, AA.carrier = torsFun C T pt) ∧ (∀ a : T.A, (∀ φ : T.A →ₐ[R] R, φ a = 0) → a = 0) ∧ (∀ x, ∃! φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x) ∧ (∀ φ : T.A →ₐ[R] R, ∃ x, spMap φ ≫ T.y = pt x) ∧ ∀ x : N, p • x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.torsion_points_hopf_order | exact GlobalTheory.CompanionTheory.Relay.torsion_points_hopf_order | (intros; apply GlobalTheory.CompanionTheory.Relay.torsion_points_hopf_order <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.lattice_families_glue_to_bundle : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V], (∀ Γ : (∀ k, ι k) → AddSubgroup V, IsLatFamily O x Γ → (∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (Γ s)) → ∃ E : ChartBundle O (mseg x) N V, ∀ s, mseg x s ≠ 0 → E.lat s = Γ s) ∧ ∀ E : ChartBundle O (mseg x) N V, IsLatFamily O x E.lat ∧ ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (E.lat s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main | exact GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing exists_pow_mul_mem_chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg restrictChart)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullExists

section Charts

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def mixChart (c : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => c k
  | .inr k => s (.inr k)

def secondChart (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k, ι' k := fun k => s (.inr k)

theorem restrictChart_mixChart (c : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    restrictChart (mixChart c s) = c := rfl

theorem secondChart_mixChart (c : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    secondChart (mixChart c s) = secondChart s := rfl

theorem mseg_joinCoord {F : Type*} [CommMonoid F] (x : (Σ k, ι k) → F) (z : (Σ k, ι' k) → F)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) s = mseg x (restrictChart s) * mseg z (secondChart s) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

end Charts

section Pull

variable {O : Type} [CommRing O] {Ω Ω₁ : Type} [Field Ω] [Field Ω₁] [Algebra O Ω] [Algebra O Ω₁]
  [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι' k) → Ω₁}

theorem mseg_bcCoord (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (bcCoord x z) s =
      algebraMap Ω Ω₁ (mseg x (restrictChart s)) * mseg z (secondChart s) := by
  rw [bcCoord, mseg_joinCoord]
  simp [mseg, map_prod]

theorem first_ne_zero {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0) :
    mseg x (restrictChart s) ≠ 0 := by
  intro h
  exact hs (by rw [mseg_bcCoord, h]; simp)

theorem second_ne_zero {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0) :
    mseg z (secondChart s) ≠ 0 := by
  intro h
  exact hs (by rw [mseg_bcCoord, h]; simp)

theorem ratio_first {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0)
    (c : ∀ k, ι k) :
    algebraMap Ω Ω₁ (mseg x c / mseg x (restrictChart s)) ∈
      chartRing O (mseg (bcCoord x z)) s := by
  have h := div_mem_chartRing (o := O) (mseg (bcCoord x z)) s (mixChart c s)
  rw [mseg_bcCoord x z (mixChart c s), mseg_bcCoord x z s, restrictChart_mixChart,
    secondChart_mixChart, mul_div_mul_right _ _ (second_ne_zero hs), ← map_div₀] at h
  exact h

theorem ratio_second {s t : ∀ k : K ⊕ K', Sum.elim ι ι' k} (ht : mseg (bcCoord x z) t ≠ 0) :
    mseg z (secondChart s) / mseg z (secondChart t) ∈ chartRing O (mseg (bcCoord x z)) t := by
  have h := div_mem_chartRing (o := O) (mseg (bcCoord x z)) t (mixChart (restrictChart t) s)
  rw [mseg_bcCoord x z (mixChart (restrictChart t) s), mseg_bcCoord x z t, restrictChart_mixChart,
    secondChart_mixChart, mul_div_mul_left _ _
      ((map_ne_zero (algebraMap Ω Ω₁)).2 (first_ne_zero ht))] at h
  exact h

theorem map_mem_chartRing {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0)
    {a : Ω} (ha : a ∈ chartRing O (mseg x) (restrictChart s)) :
    algebraMap Ω Ω₁ a ∈ chartRing O (mseg (bcCoord x z)) s := by
  have hle : chartRing O (mseg x) (restrictChart s) ≤
      (chartRing O (mseg (bcCoord x z)) s).comap (IsScalarTower.toAlgHom O Ω Ω₁) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨c, rfl⟩
    exact ratio_first hs c
  exact hle ha

variable {N : ℕ} {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω₁ V₁]
  [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁]

def pullFam (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁) (E : ChartBundle O (mseg x) N V)
    (bc : V →ₗ[Ω] V₁) : (∀ k : K ⊕ K', Sum.elim ι ι' k) → AddSubgroup V₁ := fun s =>
  spanOver (chartRing O (mseg (bcCoord x z)) s) (bc '' (E.lat (restrictChart s) : Set V))

theorem isLatFamily_pullFam (E : ChartBundle O (mseg x) N V) (bc : V →ₗ[Ω] V₁) :
    IsLatFamily O (bcCoord x z) (pullFam x z E bc) := by
  refine ⟨fun s _ a ha v hv => LocFreeBC.smul_mem_spanOver _ _ ha hv,
    fun s t hs ht v hv => ?_⟩
  have hf : mseg (bcCoord x z) s / mseg (bcCoord x z) t ∈ chartRing O (mseg (bcCoord x z)) t :=
    div_mem_chartRing _ t s
  have hst : ∀ a ∈ chartRing O (mseg (bcCoord x z)) t, ∀ e ∈ pullFam x z E bc t,
      a • e ∈ pullFam x z E bc t := fun a ha e he => LocFreeBC.smul_mem_spanOver _ _ ha he
  have hfac : mseg (bcCoord x z) s / mseg (bcCoord x z) t =
      algebraMap Ω Ω₁ (mseg x (restrictChart s) / mseg x (restrictChart t)) *
        (mseg z (secondChart s) / mseg z (secondChart t)) := by
    rw [mseg_bcCoord x z s, mseg_bcCoord x z t, map_div₀, mul_div_mul_comm]
  change v ∈ AddSubgroup.closure _ at hv
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hv
    obtain ⟨m₁, hm₁⟩ := exists_pow_mul_mem_chartRing (mseg (bcCoord x z)) s t hs ha
    obtain ⟨m₂, hm₂⟩ := E.overlap _ _ (first_ne_zero hs) (first_ne_zero ht) e he
    refine ⟨m₁ + m₂, AddSubgroup.subset_closure ⟨_, mul_mem hm₁ (pow_mem
      (ratio_second (s := s) ht) m₂), _, ⟨_, hm₂, rfl⟩, ?_⟩⟩
    rw [map_smul, ← algebraMap_smul Ω₁ (_ ^ m₂) (bc e), smul_smul, smul_smul]
    congr 1
    rw [pow_add, map_pow]
    nth_rw 2 [hfac]
    rw [mul_pow]
    ring
  | zero => exact ⟨0, by simp⟩
  | add v w _ _ hv hw => exact LocFreeBC.loc_add _ _ hst hf hv hw
  | neg v _ hv =>
    obtain ⟨n, hn⟩ := hv
    exact ⟨n, by simpa using neg_mem hn⟩

theorem locFree_pullFam (E : ChartBundle O (mseg x) N V) (bc : V →ₗ[Ω] V₁)
    (hbc : IsBaseChange Ω₁ bc) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (hs : mseg (bcCoord x z) s ≠ 0) :
    LocFree (chartRing O (mseg (bcCoord x z)) s) N (pullFam x z E bc s) := by
  classical
  exact LocFreeBC.locFree_baseChange _ _ (fun _ ha => map_mem_chartRing hs ha) bc hbc N _
    (((BundleOfFamily.main O Ω K ι x N V).2 E).2 _ (first_ne_zero hs))

theorem exists_pullBC [IsDomain O] [IsDiscreteValuationRing O] (E : ChartBundle O (mseg x) N V)
    (bc : V →ₗ[Ω] V₁) (hbc : IsBaseChange Ω₁ bc) :
    ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB := by
  classical
  obtain ⟨EB, hEB⟩ := (BundleOfFamily.main O Ω₁ (K ⊕ K') (Sum.elim ι ι') (bcCoord x z) N V₁).1
    (pullFam x z E bc) (isLatFamily_pullFam E bc) (locFree_pullFam E bc hbc)
  refine ⟨EB, fun s hs => ?_⟩
  rw [hEB s hs]
  refine congrArg AddSubgroup.closure (Set.ext fun v => ?_)
  constructor
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, e, he, rfl⟩
  · rintro ⟨a, ha, e, he, rfl⟩
    exact ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩

end Pull

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V), (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), ∃ EB : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁), IsBaseChange Ω₁ bc → ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E
  refine ⟨fun K' _ _ ι' _ z => ?_,
    fun Ω₁ _ _ _ _ K' _ _ ι' _ z V₁ _ _ _ _ bc hbc => exists_pullBC E bc hbc⟩
  exact exists_pullBC (Ω₁ := Ω) (V₁ := V) (z := z) E LinearMap.id
    (IsBaseChange.ofEquiv (LinearEquiv.refl Ω V))

end GlobalTheory.CompanionTheory.Ar.Num.PullExists
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

theorem _root_.GlobalTheory.T.hodge_tate_chart_different_generators : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (σ : E →+* K) (d : A), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → ∃ G H Z Z' : Matrix (Fin N) (Fin N) A, (∀ i j, algebraMap A K (G i j) = D.gram σ d i j) ∧ G * H = 1 + ((p : A) ^ R) • Z ∧ H * G = 1 + ((p : A) ^ R) • Z' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.gram_integral_unit_mod | exact GlobalTheory.CompanionTheory.Ar.HT.gram_integral_unit_mod | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.gram_integral_unit_mod <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.HT NumberField TensorProduct

theorem _root_.GlobalTheory.T.hodge_tate_lattice_base_change_pairing : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p R N : ℕ) (W Ω : Type) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Projective A W] [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (j : W →ₗ[A] Ω), IsBaseChange K j → ∀ (ρ : 𝓞 E →+* Module.End A W) (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)) (h : (Fin N → 𝓞 E) →+ W), (∀ x, e x x = 0) → (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv c a • y)) → (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ R), ∃ x, e x = φ) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → (∀ (a : 𝓞 E) x, ∃ y, h (a • x) = ρ a (h x) + (p ^ R) • y) → ∃ D : HTChart A K c p R N Ω, D.om = LinearMap.range j ∧ D.e = e ∧ (∀ x, D.h x = j (h x)) ∧ ∀ a w, D.ρΩ a (j w) = j (ρ a w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.htChart_of_projective_module | exact GlobalTheory.CompanionTheory.Ar.HT.htChart_of_projective_module | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.htChart_of_projective_module <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.divisible_group_from_tower : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L), ∃ (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate), X.Realises G e τ ∧ G.height = Module.finrank ℤ La ∧ ∃ j : ℤ_[p] ⊗[ℤ] La ≃ₗ[ℤ_[p]] G.Tate, ∀ a, j (1 ⊗ₜ a) = τ a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.tower_pdiv_exists | exact GlobalTheory.CompanionTheory.Ar.HT.tower_pdiv_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.tower_pdiv_exists <;> assumption)
end
