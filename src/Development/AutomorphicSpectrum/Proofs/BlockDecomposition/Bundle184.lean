module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle174
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle175
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverLatticeBase
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle151
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle135
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle168
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle155
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle169
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle170
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle176
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle117
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle153
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
import Mathlib.RepresentationTheory.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedFil

theorem exists_lift {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    {δ : DividedPowers J} {δ' : DividedPowers J'} {f : B →+* B'} (hf : IsDPMorphism δ δ' f)
    (hJ : J' = J.map f) (hs : Function.Surjective f) (l : List (ℕ × B')) (hl : ∀ q ∈ l, q.2 ∈ J') :
    ∃ l' : List (ℕ × B), (∀ q ∈ l', q.2 ∈ J) ∧ l'.map Prod.fst = l.map Prod.fst ∧
      (l.map fun q => δ'.dpow q.1 q.2).prod = f (l'.map fun q => δ.dpow q.1 q.2).prod := by
  induction l with
  | nil => exact ⟨[], by simp, rfl, by simp⟩
  | cons q l ih =>
    obtain ⟨l', h1, h2, h3⟩ := ih fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have hq := hl q List.mem_cons_self
    rw [hJ] at hq
    obtain ⟨y, hy, e⟩ := (Ideal.mem_map_iff_of_surjective f hs).1 hq
    refine ⟨(q.1, y) :: l', ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      exacts [hy, h1 p hp]
    · simp [h2]
    · simp only [List.map_cons, List.prod_cons, map_mul, h3, ← e]
      rw [hf.2 y hy]

theorem dividedPowerFiltration_le_map {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    {δ : DividedPowers J} {δ' : DividedPowers J'} {f : B →+* B'} (hf : IsDPMorphism δ δ' f)
    (hJ : J' = J.map f) (hs : Function.Surjective f) (r : ℕ) : pdP δ' r ≤ (pdP δ r).map f := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hr, rfl⟩
  obtain ⟨l', h1, h2, h3⟩ := exists_lift hf hJ hs l hl
  rw [h3]
  exact Ideal.mem_map_of_mem f (Ideal.subset_span ⟨l', h1, by rwa [h2], rfl⟩)

section
variable {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ]
  {I : Ideal A} {γ : DividedPowers I} {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ}
  (d : RedIn δ κ γ l n) {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {s : ℕ}

theorem redObj_pdPow (T : Thick (nlFun γ 0 X q (κA O I))) (h : TF l s T) (r : ℕ) :
    (redObj T d h).pdPow r ≤ (T.pdPow r).map (Ideal.Quotient.mk (lnT T l n)) :=
  dividedPowerFiltration_le_map (redδ_dp T h n) rfl Ideal.Quotient.mk_surjective r
end

def toSomeP {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : ℤ) (c : b.R) (j : ℕ) :
    HM Q none c j →ₗ[b.R] HM Q (some r) c j :=
  (sqLe (a := IdF.top _) (a' := IdF.top _) (b := stdI Q none c) (b' := stdI Q (some r) c)
    (fun _ => le_rfl) (fun T => sup_le_sup_right (bot_le : (⊥ : Ideal _) ≤ _) _)).pull j

end GlobalTheory.CompanionTheory.RedFil

namespace GlobalTheory.CompanionTheory.RedFil

section
variable {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ]
  {I : Ideal A} {γ : DividedPowers I} {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ}
  (d : RedIn δ κ γ l n) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ)
  (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
  (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))

theorem val_zero (r : ℕ) (T : (TS γ q l s 𝒱).FullSubcategory) (v : ((redG q s d 𝒱).obj T).B)
    (hv : v ∈ ((redG q s d 𝒱).obj T).pdPow r) :
    (sqLe (a := IdF.top _) (a' := IdF.top _) (b := stdI (TS γ q l s 𝒱) none ((l : A) ^ n))
      (b' := stdI (TS γ q l s 𝒱) (some (r : ℤ)) ((l : A) ^ n)) (fun _ => le_rfl)
      (fun T => sup_le_sup_right (bot_le : (⊥ : Ideal _) ≤ _) _)).τ T
      ((redMor q s d 𝒱 c lam hc none).τ T v) = 0 := by
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
    (redObj_pdPow d T.obj T.property.1 r hv)
  refine Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left ?_))
  change y ∈ T.obj.pdPow (r : ℤ).toNat
  simpa using hy

theorem red_kills (r j : ℕ) : ∀ x ∈ (B.pdS (nlFun δ l X q κ) c r).img j,
    toSomeP (TS γ q l s 𝒱) (r : ℤ) ((l : A) ^ n) j ((redMor q s d 𝒱 c lam hc none).pull j x) = 0 := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 y
  let S := B.pdS (nlFun δ l X q κ) c r
  let m := redMor q s d 𝒱 c lam hc none
  let t := sqLe (a := IdF.top _) (a' := IdF.top _) (b := stdI (TS γ q l s 𝒱) none ((l : A) ^ n))
      (b' := stdI (TS γ q l s 𝒱) (some (r : ℤ)) ((l : A) ^ n)) (fun _ => le_rfl)
      (fun T => sup_le_sup_right (bot_le : (⊥ : Ideal _) ≤ _) _)
  have h1 : CH.d _ j (S.inc.pullC j a) = 0 := by
    rw [S.inc.d_pullC]
    exact (congrArg _ ha).trans (map_zero _)
  have h2 : CH.d _ j (m.pullC j (S.inc.pullC j a)) = 0 := by
    rw [m.d_pullC, h1, map_zero]
  have h3 : CH.d _ j (t.pullC j (m.pullC j (S.inc.pullC j a))) = 0 := by
    rw [t.d_pullC, h2, map_zero]
  have e1 : S.inc.pull j ((CH.cx _).cls a ha) = (CH.cx _).cls (S.inc.pullC j a) h1 :=
    CrystallineSemistableComparison.P.mapH_cls S.inc.hom j a ha h1
  have e2 : m.pull j ((CH.cx _).cls (S.inc.pullC j a) h1) = (CH.cx _).cls (m.pullC j (S.inc.pullC j a)) h2 :=
    CrystallineSemistableComparison.P.mapH_cls m.hom j _ h1 h2
  have e3 : t.pull j ((CH.cx _).cls (m.pullC j (S.inc.pullC j a)) h2) =
      (CH.cx _).cls (t.pullC j (m.pullC j (S.inc.pullC j a))) h3 :=
    CrystallineSemistableComparison.P.mapH_cls t.hom j _ h2 h3
  have e4 : t.pullC j (m.pullC j (S.inc.pullC j a)) = 0 := by
    funext σ
    exact val_zero d q s 𝒱 c lam hc r _ _ (a (((σ ⋙ t.G) ⋙ m.G) ⋙ S.inc.G)).2
  change t.pull j (m.pull j (S.inc.pull j _)) = 0
  rw [e1, e2, e3]
  exact ((CrystallineSemistableComparison.P.cls_surj _ j).2.1 _ h3).2 (by rw [e4]; exact Submodule.zero_mem _)
end

end GlobalTheory.CompanionTheory.RedFil
end
end

section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Lat

theorem quot_pdP_no_torsion : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ (r : ℕ) (x : Lat.A f ξ l M), (l : Lat.A f ξ l M) * x ∈ pdP (Lat.γ f ξ l M hc) r → x ∈ pdP (Lat.γ f ξ l M hc) r := by
  intro W B _ _ _ f ξ l M m hH hc r x hx
  rw [GlobalTheory.T.lattice_filtration_comap_span_pow f ξ l M m hH hc r] at hx ⊢
  rw [Ideal.mem_comap, map_mul, map_natCast] at hx
  rw [Ideal.mem_comap]
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hH.l0 Nat.cast_zero
  have hl : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl0
  have hu : algebraMap ℚ B (l : ℚ)⁻¹ * (l : B) = 1 := by
    rw [← map_natCast (algebraMap ℚ B) l, ← map_mul, inv_mul_cancel₀ hl, map_one]
  have h2 := Ideal.mul_mem_left _ (algebraMap ℚ B (l : ℚ)⁻¹) hx
  rwa [← mul_assoc, hu, one_mul] at h2

end GlobalTheory.CompanionTheory.Lat
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_splitting_over_field : ∀ {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) (m : ℕ),
    pdP γ m = ⊥ → Nonempty (GrSplit K γ m) := by
  first | exact @GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit | exact GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit | (intros; apply GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.chart_tensor_base_compat : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} {d : ℕ} (cV : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) V d) (cA : Chart γ 0 q (κA O I) V d)
      (eO : O ⊗[O] Γ(X, V) ≃+* cO.D.B) (eA : A ⊗[O] Γ(X, V) ≃+* cA.D.B),
      (∀ r, eO (r ⊗ₜ 1) = cO.D.i r) → (∀ r, eA (r ⊗ₜ 1) = cA.D.i r) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (eO (1 ⊗ₜ f))) →
      (∀ f, ev cA.D cA.inV f = Ideal.Quotient.mk _ (eA (1 ⊗ₜ f))) →
      ∃ e₀ : cO.D ⟶ ((nmO γ q).mor 0).obj cA.D, ∀ f, e₀.φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f) := by
  first | exact @GlobalTheory.CompanionTheory.BcMor.chart_mor | exact GlobalTheory.CompanionTheory.BcMor.chart_mor | (intros; apply GlobalTheory.CompanionTheory.BcMor.chart_mor <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_splitting_tensor_filtration : ∀ {O A Γ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing Γ] [Algebra O Γ] [Module.Flat O Γ]
    {I : Ideal A} (γ : DividedPowers I) (m : ℕ) (S : GrSplit O γ m),
    ∃ g : (∀ i, S.N i ⊗[O] Γ) ≃ₗ[O] A ⊗[O] Γ, (∀ i n x, g (Pi.single i (n ⊗ₜ x)) = S.ν i n ⊗ₜ x) ∧
      ∀ (r : ℕ) (z : ∀ i, S.N i ⊗[O] Γ), g z ∈ (pdP γ r).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ)) ↔
        ∀ i : Fin m, (i : ℕ) < r → z i = 0 := by
  first | exact @GlobalTheory.CompanionTheory.GrTens.main | exact GlobalTheory.CompanionTheory.GrTens.main | (intros; apply GlobalTheory.CompanionTheory.GrTens.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_splitting_over_lattice_base : ∀ {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] {I : Ideal A}
    (γ : DividedPowers I) (l m : ℕ), (∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ (l : O) ^ k) → LatBase γ l m → Nonempty (GrSplit O γ m) := by
  first | exact @GlobalTheory.CompanionTheory.LatSplit.nonempty_grSplit | exact GlobalTheory.CompanionTheory.LatSplit.nonempty_grSplit | (intros; apply GlobalTheory.CompanionTheory.LatSplit.nonempty_grSplit <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge

variable {R : Type} [CommRing R] {X : Scheme.{0}}

private theorem res_res_lemma {A B C : X.Opens} (f : B ⟶ A) (g' : C ⟶ B) (s : Γ(X, A)) :
    X.presheaf.map g'.op (X.presheaf.map f.op s) = X.presheaf.map (g' ≫ f).op s := by
  rw [op_comp, Functor.map_comp]
  rfl

theorem eq_of_res_affine (W : X.Opens) (a b : Γ(X, W))
    (h : ∀ (V : X.affineOpens) (hV : V.1 ≤ W),
      X.presheaf.map (homOfLE hV).op a = X.presheaf.map (homOfLE hV).op b) : a = b := by
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i : {V : X.affineOpens // V.1 ≤ W} => i.1.1) W
    (fun i => homOfLE i.2)
  · intro x hx
    obtain ⟨V, hV, hxV, hVW⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Scheme.isBasis_affineOpens X) hx
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  · intro i
    exact h i.1 i.2

theorem exists_global (g : ∀ U : X.affineOpens, Γ(X, U.1))
    (hg : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1), X.presheaf.map (homOfLE h).op (g U) = g V) :
    ∃ t : Γ(X, ⊤), ∀ U : X.affineOpens,
      X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op t = g U := by
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf (fun i : X.affineOpens => i.1) g := by
    intro i j
    apply eq_of_res_affine
    intro V hV
    rw [res_res_lemma, res_res_lemma]
    exact (hg i V (hV.trans inf_le_left)).trans (hg j V (hV.trans inf_le_right)).symm
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i : X.affineOpens => i.1) ⊤
    (fun i => homOfLE le_top) (by
      intro x _
      obtain ⟨V, hV, hxV, -⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Scheme.isBasis_affineOpens X)
          (show x ∈ (⊤ : X.Opens) from trivial)
      rw [TopologicalSpace.Opens.mem_iSup]
      exact ⟨⟨V, hV⟩, hxV⟩) g hcompat
  exact ⟨t, ht⟩

theorem algebraMap_sec (s : X ⟶ Sp R) (U : X.Opens) (r : R) :
    algebraMap R (Sec s U) r = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := rfl

theorem stein_of_bijective (s : X ⟶ Sp R) (h : Function.Bijective s.appTop.hom) : Stein (OAff s) := by
  have key : ∀ (r : R) (U : X.affineOpens),
      (algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) (op U) = X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
    intro r U
    exact algebraMap_sec s U.1 r
  refine ⟨?_, ?_⟩
  · intro y
    constructor
    · intro hy
      have hg : ∀ (U V : X.affineOpens) (hUV : V.1 ≤ U.1),
          X.presheaf.map (homOfLE hUV).op (y (op U)) = y (op V) := by
        intro U V hUV
        have e := congrFun (congrFun (congrFun hy (op U)) (op V)) (homOfLE (show V ≤ U from hUV)).op
        have e' : (show Γ(X, V.1) from y (op V)) - X.presheaf.map (homOfLE hUV).op (y (op U)) = 0 := e
        exact (sub_eq_zero.mp e').symm
      obtain ⟨t, ht⟩ := exists_global (fun U => y (op U)) hg
      obtain ⟨x, hx⟩ := h.2 t
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x, ?_⟩
      funext T
      have hxinv : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = x :=
        congrArg (fun f => CommRingCat.Hom.hom f x) (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
      have e1 := key ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) T.unop
      rw [hxinv, hx] at e1
      exact e1.trans (ht T.unop)
    · rintro ⟨r, rfl⟩
      funext T T' φ
      have hc : (GlobalTheory.CatCoh.mp (OAff s) φ) ((algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T) =
          (algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T' := (GlobalTheory.CatCoh.mp (OAff s) φ).commutes r
      show (algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T' -
          (GlobalTheory.CatCoh.mp (OAff s) φ) ((algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T) = 0
      rw [hc, sub_self]
  · rw [injective_iff_map_eq_zero]
    intro r hr
    have e : s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = 0 := by
      apply eq_of_res_affine
      intro V hV
      rw [map_zero]
      have e2 := congrFun hr (op V)
      rw [key] at e2
      exact e2
    have e3 := h.1 (e.trans (map_zero _).symm)
    have hr2 : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r :=
      congrArg (fun f => CommRingCat.Hom.hom f r) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id
    rw [e3, map_zero] at hr2
    exact hr2.symm

theorem stein_holds : SteinSt := by
  unfold MainStatements.Hodge.SteinSt MainStatements.Hodge.AllAb
  intro R _ A _ g hA _
  exact stein_of_bijective A.hom (GlobalTheory.globalFns_holds (Sp R) A hA)

end GlobalTheory.CompanionTheory.Hodge
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix

namespace GlobalTheory.CompanionTheory.MirFourier

theorem eq_zero_of_forall_twKer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (m + 1)) V), IsSmooth τ → ∀ v : V, v ∈ twKer τ (MirUin k (m + 1)) 1 → (∀ g : GL (Fin (m + 1)) k, τ (levi k (m + 1) g) v ∈ twKer τ (MirUin k (m + 1)) (mirChar k ψ m)) → v = 0 := by
  intro k _ _ _ _ ψ hψ hψ1 m V _ _ τ hτ v h0 hg
  have hρ : IsSmooth (τ.comp (unipMir k (m + 1))) := GlobalTheory.T.mirabolic_restriction_unipotent_smooth k (m + 1) V τ hτ
  have hall : ∀ a : Fin (m + 1) → k,
      v ∈ twKer (τ.comp (unipMir k (m + 1))) ⊤ (chiOn k ψ a ⊤) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      exact mem_chi_zero ψ τ h0
    · obtain ⟨g, hgr⟩ := GlobalTheory.T.exists_invertible_matrix_last_line_given k m a ha
      have e : (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) = a := funext hgr
      have := mem_chi_row ψ τ g (hg g)
      rw [e, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
        Module.End.one_apply] at this
      exact this
  obtain ⟨N, hN⟩ := GlobalTheory.T.smooth_vector_fixed_by_small_box k (m + 1) V _ hρ v
  obtain ⟨J, hJ⟩ := GlobalTheory.T.uniform_twisted_invariance_on_ball k ψ hψ (m + 1) V _ v (addCharConductor ψ - N)
    (fun a => GlobalTheory.T.twisted_invariant_small_boxes k (m + 1) V _ (chi k ψ a) v (hall a))
  exact GlobalTheory.T.twisted_kernel_of_small_box_character k ψ hψ hψ1 (m + 1) V _ hρ v N (min J N) (min_le_right _ _) hN
    (fun a ha => hJ (min J N) (min_le_left _ _) a ha)

end GlobalTheory.CompanionTheory.MirFourier

end
end

section


theorem _root_.GlobalTheory.T.tube_chain_holds : PositivityTheory.RgEis.TubeChain := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.tubeChain | exact GlobalTheory.CompanionTheory.TubeFourier.tubeChain | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.tubeChain <;> assumption)
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

theorem _root_.GlobalTheory.T.ring_isomorphism_transports_places : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] (e : F ≃+* F'), ∃ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ^ 2 ↔ eO x ∈ (eV v).asIdeal ^ 2) ∧ ∀ v : HeightOneSpectrum (𝓞 F), normV (eV v) = normV v := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.Places.exists_places_of_ringEquiv | exact GlobalTheory.CompanionTheory.PTIso.Places.exists_places_of_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.PTIso.Places.exists_places_of_ringEquiv <;> assumption)
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

theorem _root_.GlobalTheory.T.galois_group_transport_isomorphism : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∃ Φ : G F Ω ≃ₜ* G F' Ω', ∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x) := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.exists_galContinuousMulEquiv | exact GlobalTheory.CompanionTheory.PTIso.exists_galContinuousMulEquiv | (intros; apply GlobalTheory.CompanionTheory.PTIso.exists_galContinuousMulEquiv <;> assumption)
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

theorem _root_.GlobalTheory.T.ring_equiv_transports_decomposition : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v) := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.isPlaceOver_transfer_fieldIso | exact GlobalTheory.CompanionTheory.PTIso.isPlaceOver_transfer_fieldIso | (intros; apply GlobalTheory.CompanionTheory.PTIso.isPlaceOver_transfer_fieldIso <;> assumption)
end
