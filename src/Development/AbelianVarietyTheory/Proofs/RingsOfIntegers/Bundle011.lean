module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle003
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteNotIsUnitOneAddSmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AdaptUnitary

open NumberField IsDedekindDomain
open scoped Matrix

section Genus

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.GenusSelfDual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_coprime_nsmul_mem (m : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (h : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (m : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal →
      ∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L) :
    ∃ k : ℕ, k.Coprime m ∧ k • x ∈ L := by
  let J : Ideal ℤ := (L.toAddSubgroup.toIntSubmodule).comap (LinearMap.toSpanSingleton ℤ _ x)
  have hJ : ∀ k : ℤ, k ∈ J ↔ k • x ∈ L := fun k => Iff.rfl
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal J).principal
  have hg' : ∀ k : ℤ, k • x ∈ L ↔ g ∣ k := fun k => by
    rw [← hJ, hg]; exact Ideal.mem_span_singleton
  refine ⟨g.natAbs, Nat.Coprime.symm (Nat.coprime_of_dvd fun p hp hpm hpg => ?_), ?_⟩
  · obtain ⟨k, hk, hkx⟩ := exists_nsmul_mem hp L x fun v hv => h v (by
      obtain ⟨c, rfl⟩ := hpm
      rw [Nat.cast_mul]
      exact v.asIdeal.mul_mem_right _ hv)
    rw [← natCast_zsmul, hg', ← Int.natAbs_dvd_natAbs, Int.natAbs_natCast] at hkx
    exact hk (hpg.trans hkx)
  · rw [← natCast_zsmul, hg']
    exact Int.dvd_natAbs.2 dvd_rfl


omit [NumberField E] [IsCMField E] in
theorem exists_coprime_uniform (m : ℕ) {L₁ L₂ : Submodule (𝓞 E) (Fin n → E)} (hL : L₁.FG)
    (h : ∀ x ∈ L₁, ∃ k : ℕ, k.Coprime m ∧ k • x ∈ L₂) : ∃ k : ℕ, k.Coprime m ∧ ∀ x ∈ L₁, k • x ∈ L₂ := by
  obtain ⟨s, rfl⟩ := hL
  choose k hk hkx using fun x : s => h x (Submodule.subset_span x.2)
  refine ⟨∏ x, k x, Nat.Coprime.prod_left fun x _ => hk x, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem k (Finset.mem_univ (⟨x, hx⟩ : s))
    rw [hc, mul_comm, mul_smul]
    exact nsmul_mem (hkx ⟨x, hx⟩) c
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact L₂.smul_mem a hx

theorem exists_unitary_of_selfDual [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] {Λ : Lat E n}
    (hΛ : Λ.SelfDual) {m : ℕ} (hm : m ≠ 0) :
    ∃ γ : Matrix (Fin n) (Fin n) E, (γ.map cc)ᵀ * γ = 1 ∧
      (∀ x ∈ Λ.L, ∃ k : ℕ, k.Coprime m ∧ k • (γ.map cc)ᵀ *ᵥ x ∈ stdMod E n) ∧
      ∀ y ∈ stdMod E n, ∃ k : ℕ, k.Coprime m ∧ k • γ *ᵥ y ∈ Λ.L := by
  have hL : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ.L := ⟨Λ.fg, Λ.span_top⟩
  choose h hh hhL using exists_orthonormal_frame (G := 1) (L := Λ.L)
    (fun a b => by simp [cc, Matrix.one_apply, apply_ite, eq_comm]) (by simp) hL
    (fun x => (hΛ x).trans (forall₂_congr fun y _ => by
      rw [herm_one]
      exact ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨_, h⟩, rfl⟩⟩))
  have hh' : ∀ v, ((h v).1.map (locConj v))ᵀ * (h v).1 = 1 := fun v => by
    have := congrArg Matrix.transpose (hh v)
    rwa [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_one] at this
  have hinv : ∀ v, ((h v)⁻¹).1 = ((h v).1.map (locConj v))ᵀ := fun v =>
    Units.inv_eq_of_mul_eq_one_left (hh' v)
  obtain ⟨γ, hγ, hγ'⟩ := exists_unitary_near hm (fun v => (h v).1) hh'
  have hmap : ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (M : Matrix (Fin n) (Fin n) E) (x : Fin n → E),
      (fun i => locEmb v ((M *ᵥ x) i)) = M.map (locEmb v) *ᵥ fun i => locEmb v (x i) :=
    fun v M x => funext fun i => RingHom.map_mulVec (locEmb v) M x i
  refine ⟨γ, hγ, fun x hx => exists_coprime_nsmul_mem m _ _ fun v hv => ?_,
    fun y hy => exists_coprime_nsmul_mem m _ _ fun v hv => ?_⟩
  · have h1 := (hhL v _).1 (Submodule.subset_span ⟨x, hx, rfl⟩)
    have h2 : ∀ i j, (((γ.map cc)ᵀ).map (locEmb v) * (h v).1) i j ∈ locOrder v := fun i j => by
      convert locConj_mem v (hγ' v hv j i) using 1

      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, locConj_locConj,
      locConj_locEmb, mul_comm]
    have h3 := mulVec_mem_locOrder v h2 h1
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← hmap] at h3
    exact exists_smul_mem_stdMod v h3
  · refine (locEmb_mem_locLattice_iff v hL _).1 ((hhL v _).2 ?_)
    change ∀ i, (_ *ᵥ fun i => locEmb v ((γ *ᵥ y) i)) i ∈ _
    rw [hmap, Matrix.mulVec_mulVec, hinv]
    refine mulVec_mem_locOrder v (hγ' v hv) fun i => ?_
    obtain ⟨a, ha⟩ := mem_stdMod.1 hy i
    exact ha ▸ locEmb_mem_locOrder v a


open Formalism.L2.Pj in
theorem exists_lat (Λ : GenLat E n) {N : ℕ} (hU : Λ.Unimod) (hN : 0 < N)
    (hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La) : ∃ Λ' : Lat E n, Λ'.L = Λ.La ∧ Λ'.SelfDual := by
  classical
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hs : ∀ j, (N : E) • (Pi.single j 1 : Fin n → E) ∈ Λ.La := fun j => by
    have := hle (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (single_mem_stdMod (E := E) j))
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at this
  have hin : ∀ x ∈ Λ.La, (N : E) • x ∈ stdMod E n := fun x hx => mem_stdMod.2 fun j => by
    obtain ⟨a, ha⟩ := (hU _).1 (hs j) x hx
    refine ⟨a, ha.trans ?_⟩
    simp [Pi.single_apply, apply_ite]
  have hfg : Λ.La.FG := by
    let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) := (LinearMap.lsmul E (Fin n → E) (N : E)).restrictScalars (𝓞 E)
    have hf : Function.Injective f := fun x y h => smul_right_injective _ hN' h
    refine Submodule.fg_of_fg_map_injective f hf ?_
    have h1 : (stdMod E n).FG := (Lat.std E n).fg
    refine Submodule.FG.of_le h1 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hin x hx
  refine ⟨⟨Λ.La, hfg, ?_⟩, rfl, fun x => (hU x).trans (forall₂_congr fun y _ => ?_)⟩
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have := Submodule.smul_mem _ (N : E)⁻¹ (Submodule.subset_span (R := E) (hs j))
    rw [smul_smul, inv_mul_cancel₀ hN', one_smul] at this
    simpa using this
  · have e : stdForm x y = IsCMField.complexConj E (∑ j, IsCMField.complexConj E (x j) * y j) := by
      simp [stdForm]
    have e' : (∑ j, IsCMField.complexConj E (x j) * y j) = IsCMField.complexConj E (stdForm x y) := by
      simp [stdForm]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨IsCMField.ringOfIntegersComplexConj E a, by rw [e, ← ha]; simp⟩
    · rintro ⟨a, ha⟩
      exact ⟨IsCMField.ringOfIntegersComplexConj E a, by rw [e', ← ha]; simp⟩

end Genus


open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj in
theorem exists_unitary_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ)
    (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ m : ℕ, 0 < m →
    ∃ (k : ℕ) (ga : Matrix (Fin n) (Fin n) E), Nat.Coprime k m ∧
      (∀ i j, ∑ b, IsCMField.complexConj E (ga b i) * ga b j = if i = j then 1 else 0) ∧
      (∀ v ∈ Λ.La, (k : E) • ga.mulVec v ∈ stdLat E n) ∧
      ∀ v ∈ stdLat E n, ∃ w ∈ Λ.La, (k : E) • v = ga.mulVec w := by
  intro E _ _ _ H n Λ N hU hN hle m hm
  haveI := H.unram
  obtain ⟨Λ', hΛ', hsd⟩ := exists_lat Λ hU hN hle
  obtain ⟨γ, hγ, h₁, h₂⟩ := exists_unitary_of_selfDual hsd hm.ne'
  have hγ₂ := mul_eq_one_comm.1 hγ
  let f : Matrix (Fin n) (Fin n) E → (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
    fun M => (Matrix.mulVecLin M).restrictScalars (𝓞 E)
  obtain ⟨k₁, hk₁, e₁⟩ := exists_coprime_uniform m (L₂ := GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdMod E n)
    (Λ'.fg.map (f (γ.map ReciprocityTheory.ChartRestriction.G.FD.cc)ᵀ)) (by rintro _ ⟨x, hx, rfl⟩; exact h₁ x hx)
  obtain ⟨k₂, hk₂, e₂⟩ := exists_coprime_uniform m (L₂ := Λ'.L)
    ((GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.Lat.std E n).fg.map (f γ)) (by rintro _ ⟨x, hx, rfl⟩; exact h₂ x hx)
  refine ⟨k₁ * k₂, (γ.map ReciprocityTheory.ChartRestriction.G.FD.cc)ᵀ, Nat.Coprime.mul_left hk₁ hk₂, fun i j => ?_, fun v hv => ?_,
    fun v hv => ⟨(k₁ * k₂) • γ *ᵥ v, ?_, ?_⟩⟩
  · have := congrFun (congrFun hγ₂ i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
  · rw [Nat.cast_smul_eq_nsmul, mul_comm, mul_smul]
    exact nsmul_mem (e₁ _ ⟨v, hΛ' ▸ hv, rfl⟩) k₂
  · rw [mul_smul, ← hΛ']
    exact nsmul_mem (e₂ _ ⟨v, hv, rfl⟩) k₁
  · rw [← Nat.cast_smul_eq_nsmul E, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hγ, Matrix.one_mulVec]

end GlobalTheory.AdaptUnitary
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
noncomputable def chartPullPullLinComb {X X' Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (pr : K → (X' ⟶ X)) (ε : K → ℤ) (F : Y ⟶ X') (g : Z ⟶ X) (p : K → (Y ⟶ Z))
    (hc : ∀ k, p k ≫ g = F ≫ pr k) :
    ChartPull ((LB.LinComb L pr ε).pull F) (LB.LinComb (L.pull g) p ε) (𝟙 Y) :=
  have le : ∀ J : PUnit → K → L.ι, ((LB.LinComb L pr ε).pull F).U J ≤
      LB.wchart (L.pull g) p (fun k _ => J PUnit.unit k) := fun J y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => by
      have h1 : (F ≫ pr k) y ∈ L.U (J PUnit.unit k) :=
        Set.mem_iInter.1 (Set.mem_iInter.1 hy PUnit.unit) k
      rw [← hc k] at h1
      exact h1
  { idx := fun J k _ => J PUnit.unit k
    le := le
    g := fun y J J' hj hj' => by
      refine (gm_pull_g (LB.LinComb L pr ε) F (𝟙 Y) y J J' hj hj').trans ?_
      refine (gm_linComb L pr ε (𝟙 Y ≫ F) y _ _ (Set.mem_iInter.1 hj PUnit.unit)
        (Set.mem_iInter.1 hj' PUnit.unit)).trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb (L.pull g) p ε (𝟙 Y) y _ _ (le J hj) (le J' hj')).symm)
      refine Eq.trans ?_ (gm_pull_g L g (𝟙 Y ≫ p k) y _ _ (Set.mem_iInter.1 (le J hj) k)
        (Set.mem_iInter.1 (le J' hj') k)).symm
      rw [Category.assoc, Category.assoc, hc] }

theorem isMonHom_of_isPowGrp {S : Scheme.{0}} {H G' G : Over S} [GrpObj H] [GrpObj G'] [GrpObj G]
    {j : ℕ} (p : IsPowGrp G' G j) (f : H ⟶ G') (hf : ∀ i, IsMonHom (f ≫ p.pr i)) : IsMonHom f := by
  have ext : ∀ (a b : H ⊗ H ⟶ G'), (∀ i, a ≫ p.pr i = b ≫ p.pr i) → a = b :=
    fun a b h => Fan.IsLimit.hom_ext p.lim a b h
  have ext1 : ∀ (a b : 𝟙_ (Over S) ⟶ G'), (∀ i, a ≫ p.pr i = b ≫ p.pr i) → a = b :=
    fun a b h => Fan.IsLimit.hom_ext p.lim a b h
  constructor
  · refine ext1 _ _ fun i => ?_
    rw [Category.assoc, (hf i).one_hom, (p.hom i).one_hom]
  · refine ext _ _ fun i => ?_
    rw [Category.assoc, (hf i).mul_hom, Category.assoc, (p.hom i).mul_hom, ← Category.assoc (f ⊗ₘ f),
      tensorHom_comp_tensorHom]

theorem exists_iso_of_isPowGrp {S : Scheme.{0}} {H' H G' G : Over S} [GrpObj H'] [GrpObj H]
    [GrpObj G'] [GrpObj G] {j : ℕ} (q : IsPowGrp H' H j) (p : IsPowGrp G' G j) (e : H ≅ G)
    [IsMonHom e.hom] :
    ∃ e' : H' ≅ G', IsMonHom e'.hom ∧ ∀ i, e'.hom ≫ p.pr i = q.pr i ≫ e.hom := by
  let u : H' ⟶ G' := Fan.IsLimit.lift p.lim fun i => q.pr i ≫ e.hom
  let v : G' ⟶ H' := Fan.IsLimit.lift q.lim fun i => p.pr i ≫ e.inv
  have hu : ∀ i, u ≫ p.pr i = q.pr i ≫ e.hom := fun i => Fan.IsLimit.fac p.lim _ i
  have hv : ∀ i, v ≫ q.pr i = p.pr i ≫ e.inv := fun i => Fan.IsLimit.fac q.lim _ i
  have huv : u ≫ v = 𝟙 H' := Fan.IsLimit.hom_ext q.lim _ _ fun i => by
    change (u ≫ v) ≫ q.pr i = 𝟙 H' ≫ q.pr i
    rw [Category.assoc, hv i, ← Category.assoc, hu i, Category.assoc, e.hom_inv_id, Category.comp_id,
      Category.id_comp]
  have hvu : v ≫ u = 𝟙 G' := Fan.IsLimit.hom_ext p.lim _ _ fun i => by
    change (v ≫ u) ≫ p.pr i = 𝟙 G' ≫ p.pr i
    rw [Category.assoc, hu i, ← Category.assoc, hv i, Category.assoc, e.inv_hom_id, Category.comp_id,
      Category.id_comp]
  refine ⟨⟨u, v, huv, hvu⟩, ?_, hu⟩
  refine isMonHom_of_isPowGrp p _ fun i => ?_
  have : IsMonHom (q.pr i) := q.hom i
  change IsMonHom (u ≫ p.pr i)
  rw [hu i]
  infer_instance


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_gen_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G), ∃ gen' : (Over.pullback (jK R)).obj G' ≅ A'.A, IsMonHom gen'.hom ∧ (∀ i, gen'.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ ∃ w : LB.Iso (A'.L.pull gen'.hom.left) ((boxLB U.LG.L pG.pr).pull (pullback.fst G'.hom (jK R))), w.IsGen := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U
  have : IsMonHom U.gen.hom := U.gen_hom
  obtain ⟨p', hp'⟩ := isPowGrp_baseChange _ _ (jK R) G' G j pG
  obtain ⟨e', he', hc⟩ := exists_iso_of_isPowGrp p' pA.toIsPowGrp U.gen
  refine ⟨e', he', fun i => by rw [hc i, hp' i], ?_⟩
  obtain ⟨w0, hw0⟩ := U.ext
  have pullCP : ∀ {X Y : Scheme.{0}} (L : LB X) (F : Y ⟶ X), ChartPull (L.pull F) L F := fun L F =>
    { idx := fun J => J PUnit.unit
      le := fun J y hy => (mem_pull (L := L) (F := F) (x := y) (J := J)).1 hy
      g := fun y J J' hj hj' => (gm_pull_g L F (𝟙 _) y J J' hj hj').trans (by rw [Category.id_comp]) }
  have hcA : ∀ k, (p'.pr k).left ≫ U.gen.hom.left = e'.hom.left ≫ (pA.pr k).left := fun k => by
    simpa using (congrArg (fun m => m.left) (hc k)).symm
  have hcG : ∀ k, (p'.pr k).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R) ≫ (pG.pr k).left := fun k => by
    rw [hp' k]
    simp
  have H34 : LBIso (LB.LinComb (A.L.pull U.gen.hom.left) (fun k => (p'.pr k).left) (fun _ => 1))
      (LB.LinComb (U.LG.L.pull (pullback.fst G.hom (jK R))) (fun k => (p'.pr k).left) (fun _ => 1)) :=
    ⟨LB.linCombIso w0 _ _, linCombIso_isGen w0 hw0 _ _⟩
  have HB : LBIso ((boxLB A.L pA.pr).pull e'.hom.left)
      ((boxLB U.LG.L pG.pr).pull (pullback.fst G'.hom (jK R))) :=
    LBIso.chartPull
      (chartPullPullLinComb A.L (fun k => (pA.pr k).left) (fun _ => 1) e'.hom.left U.gen.hom.left
        (fun k => (p'.pr k).left) hcA)
      (chartPullPullLinComb U.LG.L (fun k => (pG.pr k).left) (fun _ => 1) (pullback.fst G'.hom (jK R))
        (pullback.fst G.hom (jK R)) (fun k => (p'.pr k).left) hcG) H34
  have HA : LBIso (A'.L.pull e'.hom.left) ((boxLB A.L pA.pr).pull e'.hom.left) :=
    LBIso.chartPull (pullCP A'.L e'.hom.left) (pullCP _ e'.hom.left) ⟨pA.w, pA.w_gen⟩
  exact LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (linComb_isLB _ A.isLB _ _) _)
    (pull_isLB (linComb_isLB _ U.LG.isLB _ _) _) HA HB

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowPrimitive

open Geo.Tor

def chartPullSwap {X X' : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K] (F : J → (X' ⟶ X))
    (φ : K → (X ⟶ X)) (ψ : K → (X' ⟶ X')) (ε : K → ℤ) (hc : ∀ k i, ψ k ≫ F i = F i ≫ φ k) :
    ChartPull (LB.LinComb (LB.LinComb L F (fun _ => 1)) ψ ε) (LB.LinComb (LB.LinComb L φ ε) F (fun _ => 1)) (𝟙 X') :=
  have le : ∀ j : K → J → L.ι, LB.wchart (LB.LinComb L F (fun _ => 1)) ψ j ≤
      (𝟙 X') ⁻¹ᵁ LB.wchart (LB.LinComb L φ ε) F (fun i k => j k i) :=
    fun j y hy => Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun k => by
      have h : (ψ k ≫ F i) y ∈ L.U (j k i) := Set.mem_iInter.1 (Set.mem_iInter.1 hy k) i
      rw [hc] at h
      exact h
  { idx := fun j i k => j k i
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb (LB.LinComb L F (fun _ => 1)) ψ ε (𝟙 X') y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb (LB.LinComb L φ ε) F (fun _ => 1) (𝟙 X') y _ _ (le j hj) (le j' hj')).symm)
      refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k)
        (gm_linComb L F (fun _ => 1) (𝟙 X' ≫ ψ k) y (j k) (j' k)
          (Set.mem_iInter.1 hj k) (Set.mem_iInter.1 hj' k))).trans ?_
      refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ => congrArg (· ^ (1 : ℤ))
        (gm_linComb L φ ε (𝟙 X' ≫ F i) y (fun k => j k i) (fun k => j' k i)
          (Set.mem_iInter.1 (le j hj) i) (Set.mem_iInter.1 (le j' hj') i))).symm
      simp only [zpow_one, Category.id_comp, hc, ← Finset.prod_zpow]
      exact Finset.prod_comm }

theorem lbIso_linComb {X Y : Scheme.{0}} {L M : LB X} (h : LBIso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : LBIso (LB.LinComb L φ ε) (LB.LinComb M φ ε) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨LB.linCombIso u φ ε, linCombIso_isGen u hu φ ε⟩

private lemma foldr_padd_comp_eq_comp_foldr_padd {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] (h : G' ⟶ G) [IsMonHom h]
    {n : ℕ} (x' : Fin n → (G' ⟶ G')) (x : Fin n → (G ⟶ G)) (hx : ∀ k, x' k ≫ h = h ≫ x k) (l : List (Fin n)) :
    List.foldr (fun k acc => padd G' (x' k) acc) (pzero G' G') l ≫ h =
      h ≫ List.foldr (fun k acc => padd G (x k) acc) (pzero G G) l := by
  induction l with
  | nil =>
    rw [List.foldr_nil, List.foldr_nil, show pzero G' G' = 1 from Over.OverMorphism.ext rfl,
      show pzero G G = 1 from Over.OverMorphism.ext rfl, one_comp, comp_one]
  | cons k l ih =>
    rw [List.foldr_cons, List.foldr_cons, show ∀ a b : G' ⟶ G', padd G' a b = a * b from fun _ _ => Over.OverMorphism.ext rfl,
      show ∀ a b : G ⟶ G, padd G a b = a * b from fun _ _ => Over.OverMorphism.ext rfl, mul_comp, comp_mul, hx k, ih]

theorem lbIso_cube_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (boxLB L p.pr) → ∀ (f : G ⟶ G) (f' : G' ⟶ G'), (∀ i, f' ≫ p.pr i = p.pr i ≫ f) → Geo.Tor.LBIso L (cubeLB G ![𝟙 G, f] L) → Geo.Tor.LBIso L' (cubeLB G' ![𝟙 G', f'] L') := by
  intro S G' G _ _ _ _ j p L L' hL hL' hbox f f' hc hprim
  unfold cubeLB boxLB at *
  have hcomm : ∀ (I : ULift.{0} (Finset (Fin 2))) (i : Fin j),
      (psum G' ![𝟙 G', f'] I.down).left ≫ (p.pr i).left = (p.pr i).left ≫ (psum G ![𝟙 G, f] I.down).left := by
    intro I i
    have := p.hom i
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    unfold psum
    refine foldr_padd_comp_eq_comp_foldr_padd (p.pr i) _ _ (fun k => ?_) _
    fin_cases k
    · simp
    · simpa using hc i
  have hP := linComb_isLB _ hL (fun i => (p.pr i).left) (fun _ => (1 : ℤ))
  have hQ := linComb_isLB _ (linComb_isLB _ hL (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![𝟙 G, f] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))) (fun i => (p.pr i).left) (fun _ => (1 : ℤ))
  have hR := linComb_isLB _ hP (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))
  have h1 := lbIso_linComb hbox (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))
  have h3 := lbIso_linComb hprim (fun i => (p.pr i).left) (fun _ => (1 : ℤ))
  have cp := chartPullSwap L (fun i => (p.pr i).left) (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![𝟙 G, f] I.down).left)
    (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card)) hcomm
  have h2 : LBIso (LB.LinComb (LB.LinComb L (fun i => (p.pr i).left) (fun _ => (1 : ℤ)))
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
      (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card)))
      (LB.LinComb (LB.LinComb L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![𝟙 G, f] I.down).left)
        (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))) (fun i => (p.pr i).left) (fun _ => (1 : ℤ))) := by
    have hQQ := LBIso.trans hQ hP hQ (LBIso.symm h3) h3
    exact LBIso.chartPull (h := 𝟙 G'.left) cp (chartPullId _) hQQ
  exact LBIso.trans hL' hQ (linComb_isLB _ hL' _ _) (LBIso.trans hL' hP hQ hbox h3)
    (LBIso.trans hQ hR (linComb_isLB _ hL' _ _) (LBIso.symm h2) (LBIso.symm h1))

end GlobalTheory.PowPrimitive
end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IndivisibleSection

theorem exists_secBGenerates : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) (D : DegData R I), ∃ b : D.toPre.SecB 1 0, SecBGenerates (D := D) 1 0 b :=
  fun hS _ _ _ _ _ _ D => exists_generator D.toPre hS

end GlobalTheory.IndivisibleSection
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.integralDegenerationFamily_baseChange_extensionField : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (k : ℕ) (E : Fam D.toPre (FractionRing R) k) (g : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], ∃ θ : Fam D.toPre F k, ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (θ.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre F).left 1 := by
  first | exact @GlobalTheory.FamBaseChange.main | exact GlobalTheory.FamBaseChange.main | (intros; apply GlobalTheory.FamBaseChange.main <;> assumption)
end
