module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1437
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyMaximalCompactCasimirKillsKType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.adelic_l2_eq_zero_imp_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ D ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.l2A F μ D = 0 → D = 0 := by
  first | exact @GlobalTheory.WeilL2Words.eq_zero_of_l2A_eq_zero | exact GlobalTheory.WeilL2Words.eq_zero_of_l2A_eq_zero | (intros; apply GlobalTheory.WeilL2Words.eq_zero_of_l2A_eq_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.adelic_l2_limit_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _))
    (D : (κ → AdeleRing (𝓞 F) F) → ℂ) (G : ℕ → (κ → AdeleRing (𝓞 F) F) → ℂ), (∀ n, G n ∈ GlobalTheory.WeilM.schA F κ) →
    (∀ a, Filter.Tendsto (fun n => G n a) Filter.atTop (nhds (D a))) →
    Filter.Tendsto (fun n => GlobalTheory.WeilL2Words.l2A F μ (G n)) Filter.atTop (nhds 0) → GlobalTheory.WeilL2Words.l2A F μ D = 0 := by
  first | exact @GlobalTheory.WeilL2Words.l2A_eq_zero_of_tendsto | exact GlobalTheory.WeilL2Words.l2A_eq_zero_of_tendsto | (intros; apply GlobalTheory.WeilL2Words.l2A_eq_zero_of_tendsto <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.schroedingerOperator_archimedean_mem_adelicSchwartz : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F h) φ ∈ GlobalTheory.WeilM.schA F κ := by
  first | exact @GlobalTheory.WeilL2Words.schr_archPair_mem_schA | exact GlobalTheory.WeilL2Words.schr_archPair_mem_schA | (intros; apply GlobalTheory.WeilL2Words.schr_archPair_mem_schA <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GtBasis

open GlobalTheory.TorusModel

section Tangent

variable {R : Type} [CommRing R]

def redO (R : Type) [CommRing R] : baseOver (Sp R) ⟶ epsR R := Over.homMk (redE R) GlobalTheory.MBLow.GtVec.red_comp

theorem isTangent_iff {G : Over (Sp R)} [GrpObj G] (y : epsR R ⟶ G) : IsTangent y ↔ redO R ≫ y = 1 := by
  constructor
  · intro h
    apply Over.OverMorphism.ext
    refine h.trans ?_
    simp [Hom.one_def]
  · intro h
    have := congrArg (·.left) h
    refine this.trans ?_
    simp [Hom.one_def]

theorem redO_scale (c : R) : redO R ≫ epsScale R c = redO R := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap _ = spMap _
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  simp [epsScaleR]

variable {G : Over (Sp R)} [GrpObj G]

theorem isTangent_mul {y y' : epsR R ⟶ G} (h : IsTangent y) (h' : IsTangent y') : IsTangent (y * y') := by
  rw [isTangent_iff] at *
  rw [MonObj.comp_mul, h, h', _root_.mul_one]

theorem isTangent_inv {y : epsR R ⟶ G} (h : IsTangent y) : IsTangent y⁻¹ := by
  rw [isTangent_iff] at *
  rw [GrpObj.comp_inv, h, inv_one]

theorem isTangent_scale (c : R) {y : epsR R ⟶ G} (h : IsTangent y) : IsTangent (epsScale R c ≫ y) := by
  rw [isTangent_iff] at *
  rw [← Category.assoc, redO_scale, h]

theorem isTangent_tanComb {m : ℕ} (c : Fin m → R) {v : Fin m → (epsR R ⟶ G)} (h : ∀ i, IsTangent (v i)) :
    IsTangent (tanComb c v) := by
  unfold tanComb
  refine List.prod_induction (fun y => IsTangent y) (fun _ _ => isTangent_mul) ?_ ?_
  · exact (isTangent_iff _).2 (MonObj.comp_one _)
  · intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact isTangent_scale _ (h i)

theorem eq_tanComb' {m : ℕ} {c : Fin m → R} {v : Fin m → (epsR R ⟶ G)} {w : epsR R ⟶ G} (h : IsLieComb c v w) :
    w = tanComb c v := by
  obtain ⟨u, hu, rfl⟩ := h
  unfold tanComb
  congr 2
  exact funext fun i => Over.OverMorphism.ext (hu i)

end Tangent

section Stalk

variable {R : Type} [CommRing R]

theorem gs_id_eq (z : Sp R) (a : R) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 (Sp R)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = toStkA z a := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq _ z ⊤ trivial]
  simp [toStkA]
  rfl

theorem dn_inj [IsLocalRing (DualNumber R)] {a a' : R}
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 (Sp (DualNumber R))) (cpt (DualNumber R)) ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a)) =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 (Sp (DualNumber R))) (cpt (DualNumber R)) ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a'))) : a = a' := by
  rw [gs_id_eq, gs_id_eq] at h
  exact TrivSqZeroExt.inr_injective (add_left_cancel (toStkA_injective h))

end Stalk

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ D.X) (x : Fin D.P.g ⊕ Fin r → (epsR R ⟶ H)), IsLieBasis vB → (∀ j, GtTan (Φ _ (x j))) → (∀ i, (Φ _ (x (Sum.inl i))).b = vB i) → (∀ l, (Φ _ (x (Sum.inr l))).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x (Sum.inr l))).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr ((bX.repr χ l : ℤ) : R)))) → ∀ (n : ℕ) (σ : Fin n ≃ Fin D.P.g ⊕ Fin r), IsLieBasis (fun k => x (σ k)) := by
  intro R _ _ _ D H _ _ Φ hΦ r vB bX x hvB htan hb htor n σ
  have hz : ∀ T, (Φ T 1).IsZero := fun T => GtVec.isZero_of_isAdd (by simpa using hΦ.2 T 1 1)
  have bpull : ∀ (T T' : Over (Sp R)) (k : T' ⟶ T) (y : T ⟶ H), (Φ T' (k ≫ y)).b = k ≫ (Φ T y).b :=
    fun T T' k y => ((isPull_iff _ _ _).1 (hΦ.1 T' T k y)).1
  have gtan : ∀ y : epsR R ⟶ H, GtTan (Φ _ y) ↔ IsTangent y := by
    intro y
    rw [isTangent_iff]
    exact ⟨fun ⟨o, ho, h⟩ => (Φ _).injective ((isPull_unique (hΦ.1 _ _ (redO R) y) h).trans
      (GtVec.isZero_unique ho (hz _))), fun h => ⟨Φ _ 1, hz _, h ▸ hΦ.1 _ _ (redO R) y⟩⟩
  let β : (epsR R ⟶ H) →* (epsR R ⟶ D.P.A) :=
    { toFun := fun y => (Φ _ y).b
      map_one' := (hz _).1
      map_mul' := fun y y' => ((TorusModel.isAdd_iff _ _ _).1 (hΦ.2 _ y y')).1 }
  have βapp : ∀ y, β y = (Φ _ y).b := fun _ => rfl
  have βcomb : ∀ {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ H)),
      β (tanComb c v) = tanComb c (fun i => β (v i)) := by
    intro m c v
    simp only [tanComb, map_list_prod, List.map_ofFn]
    congr 1
    exact List.ofFn_inj.2 (funext fun i => bpull _ _ _ _)
  have βtan : ∀ y, IsTangent y → IsTangent (β y) := fun y h => (isTangent_iff _).2 (by
    rw [βapp, ← bpull, (isTangent_iff y).1 h]
    exact (hz _).1)
  have xtan : ∀ j, IsTangent (x j) := fun j => (gtan _).1 (htan j)
  have tor := GlobalTheory.T.torusTangentCombination_characterValues R D H Φ hΦ r (fun l χ => ((bX.repr χ l : ℤ) : R)) (fun l => x (Sum.inr l)) htor
  have split : ∀ c : Fin n → R, tanComb c (fun k => x (σ k)) =
      tanComb (fun i => c (σ.symm (Sum.inl i))) (fun i => x (Sum.inl i)) *
        tanComb (fun l => c (σ.symm (Sum.inr l))) (fun l => x (Sum.inr l)) := by
    intro c
    simp only [tanComb, List.prod_ofFn]
    have e := Equiv.prod_comp σ (fun j => epsScale R (c (σ.symm j)) ≫ x j)
    simp only [Equiv.symm_apply_apply] at e
    rw [e, Fintype.prod_sum_type]
  have βA : ∀ a : Fin D.P.g → R, β (tanComb a (fun i => x (Sum.inl i))) = tanComb a vB := by
    intro a
    rw [βcomb]
    simp only [βapp, hb]
  have βB : ∀ d : Fin r → R, β (tanComb d (fun l => x (Sum.inr l))) = 1 := fun d => (tor d).1
  have : IsLocalRing (DualNumber R) := GlobalTheory.MBLow.TanLift.isLocalRing_dualNumber R
  obtain ⟨J₀, hJ₀⟩ := TorusCoord.exists_good' D.P.isLB (cpt (DualNumber R))

  have uniq : ∀ c c' : Fin n → R, tanComb c (fun k => x (σ k)) = tanComb c' (fun k => x (σ k)) → c = c' := by
    intro c c' h
    rw [split, split] at h
    have hA := congrArg β h
    rw [map_mul, map_mul, βA, βA, βB, βB, _root_.mul_one, _root_.mul_one] at hA
    have ha : (fun i => c (σ.symm (Sum.inl i))) = (fun i => c' (σ.symm (Sum.inl i))) := by
      refine (hvB.2 _ (isTangent_tanComb _ hvB.1)).unique (isLieComb_tanComb _ _) ?_
      rw [hA]
      exact isLieComb_tanComb _ _
    rw [ha, mul_right_inj] at h
    have he : ∀ l, c (σ.symm (Sum.inr l)) = c' (σ.symm (Sum.inr l)) := by
      intro l
      have v1 := (tor (fun l => c (σ.symm (Sum.inr l)))).2 (bX l) _ (𝟙 _) _ J₀ hJ₀
      have v2 := (tor (fun l => c' (σ.symm (Sum.inr l)))).2 (bX l) _ (𝟙 _) _ J₀ hJ₀
      rw [h] at v1
      have := dn_inj (v1.symm.trans v2)
      simp only [Module.Basis.repr_self, Finsupp.single_apply] at this
      simpa using this
    funext k
    obtain ⟨j, rfl⟩ := σ.symm.surjective k
    rcases j with i | l
    · exact congrFun ha i
    · exact he l
  refine ⟨fun k => xtan (σ k), fun w hw => ?_⟩
  obtain ⟨c₁, hc₁, -⟩ := hvB.2 (β w) (βtan w hw)
  have hw₁ : β (tanComb c₁ (fun i => x (Sum.inl i))) = β w := by
    rw [βA]
    exact (eq_tanComb' hc₁).symm
  have tw' : IsTangent (w * (tanComb c₁ (fun i => x (Sum.inl i)))⁻¹) :=
    isTangent_mul hw (isTangent_inv (isTangent_tanComb _ fun i => xtan _))
  have bw' : (Φ _ (w * (tanComb c₁ (fun i => x (Sum.inl i)))⁻¹)).b = DegPre.zeroT D (epsR R) := by
    rw [← βapp, map_mul, map_inv, hw₁, mul_inv_cancel]
    rfl
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.torusExtensionTangent_characterValues_additive R D _ ((gtan _).2 tw') bw'
  have hl : ∀ χ, lam χ = ∑ l, lam (bX l) * ((bX.repr χ l : ℤ) : R) := by
    intro χ
    conv_lhs => rw [← bX.sum_repr χ]

    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  obtain ⟨bd, vd⟩ := tor (fun l => lam (bX l))
  have e : w * (tanComb c₁ (fun i => x (Sum.inl i)))⁻¹ = tanComb (fun l => lam (bX l)) (fun l => x (Sum.inr l)) :=
    (Φ _).injective (pt_ext (bw'.trans bd.symm) fun χ y J hJ => Units.ext ((hlam χ _ _ y J hJ).trans
      ((congrArg _ (by rw [hl χ])).trans (vd χ _ _ y J hJ).symm)))
  have hw : w = tanComb (fun k => Sum.elim c₁ (fun l => lam (bX l)) (σ k)) (fun k => x (σ k)) := by
    rw [split]
    simp only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr]
    rw [← e, mul_comm w, mul_inv_cancel_left]
  refine ⟨_, hw ▸ isLieComb_tanComb _ _, fun c hc => ?_⟩
  exact uniq _ _ ((eq_tanComb' hc).symm.trans hw)

end GlobalTheory.GtBasis

end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mapMatrix_secMatInf (ρ : Fin n) (j : InfinitePlace E → Fin n) (v : Fin n → Cinf E) (w : InfinitePlace E) :
    (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix (Matrix.of (secMatInf ρ j v)) =
      Matrix.of (secMat ρ (j w) (fun l => v l w)) := by
  ext i l; rfl

theorem isUnit_secMatInf (ρ : Fin n) (j : InfinitePlace E → Fin n) (hj : ∀ w, j w ≤ ρ) (v : Fin n → Cinf E)
    (hv : ∀ w, v (j w) w ≠ 0) : IsUnit (Matrix.of (secMatInf ρ j v)) := by
  rw [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
  intro w
  have h := RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) (Matrix.of (secMatInf ρ j v))
  rw [mapMatrix_secMatInf] at h
  have hu := isUnit_secMat ρ (j w) (hj w) (fun l => v l w) (hv w)
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  have h' : (Matrix.of (secMatInf ρ j v)).det w = (Matrix.of (secMat ρ (j w) (fun l => v l w))).det := h
  rw [h']
  exact hu

theorem secMatInf_mem_lev (ρ : Fin n) (j : InfinitePlace E → Fin n) (hj : ∀ w, j w ≤ ρ) (v : Fin n → Cinf E)
    (hv : ∀ w, v (j w) w ≠ 0) : toGLInf (Matrix.of (secMatInf ρ j v)) ∈ levSetInf E n (ρ + 1) := by
  rw [mem_levSetInf, val_toGLInf (isUnit_secMatInf ρ j hj v hv)]
  intro i hi
  have hiρ : ρ < i := by rw [Fin.lt_def]; omega
  refine ⟨fun l hl => funext fun w => ?_, funext fun w => ?_⟩
  · change secMat ρ (j w) (fun l => v l w) i l = 0
    rw [secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' (hj w) hiρ, if_neg hl.ne]
  · change secMat ρ (j w) (fun l => v l w) i i = 1
    rw [secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' (hj w) hiρ, if_pos rfl]

theorem rowCutInf_apply (ρ : Fin n) (g : GL (Fin n) (Cinf E)) (w : InfinitePlace E) (l : Fin n) :
    rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) l w = rowCut ρ ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) l := by
  unfold rowCutInf rowCut
  split_ifs <;> rfl

def secLinInf (ρ : Fin n) : (Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v i l => if i = ρ ∧ l ≤ ρ then v l else 0
      map_add' := fun v w => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h]
      map_smul' := fun c v => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h] }

theorem secMatInf_eq_add (ρ : Fin n) (j : InfinitePlace E → Fin n) (v : Fin n → Cinf E) :
    secMatInf ρ j v = secMatInf ρ j 0 + secLinInf ρ v := by
  funext i l w
  by_cases hi : i = ρ
  · subst hi
    by_cases hl : l ≤ i <;> simp [secMatInf, secMat, secLinInf, hl]
  · simp [secMatInf, secMat, secLinInf, hi]

theorem secMatInf_main : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n) (j : InfinitePlace E → Fin n), (∀ w, j w ≤ ρ) → (∀ v : Fin n → Cinf E, (∀ w, v (j w) w ≠ 0) → IsUnit (Matrix.of (secMatInf ρ j v)) ∧ toGLInf (Matrix.of (secMatInf ρ j v)) ∈ levSetInf E n (ρ + 1)) ∧ (∀ g ∈ levSetInf E n (ρ + 1), (∀ w, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) (j w) w ≠ 0) → g * (toGLInf (Matrix.of (secMatInf ρ j (rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))))))⁻¹ ∈ levSetInf E n ρ) ∧ ∃ L : (Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E), ∀ v, secMatInf ρ j v = secMatInf ρ j 0 + L v := by
  intro E _ _ n ρ j hj
  refine ⟨fun v hv => ⟨isUnit_secMatInf ρ j hj v hv, secMatInf_mem_lev ρ j hj v hv⟩, ?_, secLinInf ρ, secMatInf_eq_add ρ j⟩
  intro g hg hgj w
  set v := rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) with hvdef
  have hS := isUnit_secMatInf ρ j hj v hgj
  have hne : rowCut ρ ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (j w) ≠ 0 := by
    rw [← rowCutInf_apply]; exact hgj w
  have hcomp : compGL w (toGLInf (Matrix.of (secMatInf ρ j v))) =
      toGL (Matrix.of (secMat ρ (j w) (rowCut ρ ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)))) := by
    have hu := isUnit_secMat ρ (j w) (hj w) _ hne
    apply Units.ext
    rw [val_toGL hu]
    ext i l
    rw [compGL_apply, val_toGLInf hS]
    change secMat ρ (j w) (fun l => v l w) i l = _
    congr 1
    funext l
    exact rowCutInf_apply ρ g w l
  rw [map_mul, map_inv, hcomp]
  exact (secMat_main n ρ (j w) (hj w)).2.1 (compGL w g) (hg w) hne

end GlobalTheory.JSW.MirCinf
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

theorem _root_.GlobalTheory.T.exists_poly_maximalCompactCasimir_kills_KType : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (W : Submodule ℂ (Kinf E a → ℂ)),
    FiniteDimensional ℂ W → ∃ q : Polynomial ℂ, q ≠ 0 ∧ ∀ φ : Sm E a,
      (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ W) → Polynomial.aeval (casKOp E a) q φ = 0 := by
  first | exact @GlobalTheory.HCKTypes.exists_casK_poly | exact GlobalTheory.HCKTypes.exists_casK_poly | (intros; apply GlobalTheory.HCKTypes.exists_casK_poly <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.tensorPolynomialsToProductVariables_comp_mulLeft_X : ∀ (W Λ : Type) [Fintype W] [DecidableEq W] (w : W) (l : Λ),
    GlobalTheory.CCRFock.polMap W Λ ∘ₗ GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
                 (LinearMap.mulLeft ℂ (MvPolynomial.X l)) =
      LinearMap.mulLeft ℂ (MvPolynomial.X (w, l)) ∘ₗ GlobalTheory.CCRFock.polMap W Λ := by
  first | exact @GlobalTheory.CCRFock.polMap_comp_atPl_mulLeft_X | exact GlobalTheory.CCRFock.polMap_comp_atPl_mulLeft_X | (intros; apply GlobalTheory.CCRFock.polMap_comp_atPl_mulLeft_X <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.tensorPolynomialsToProductVariables_comp_pderiv : ∀ (W Λ : Type) [Fintype W] [DecidableEq W] (w : W) (l : Λ),
    GlobalTheory.CCRFock.polMap W Λ ∘ₗ GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
                 (MvPolynomial.pderiv l).toLinearMap =
      (MvPolynomial.pderiv (w, l)).toLinearMap ∘ₗ GlobalTheory.CCRFock.polMap W Λ := by
  first | exact @GlobalTheory.CCRFock.polMap_comp_atPl_pderiv | exact GlobalTheory.CCRFock.polMap_comp_atPl_pderiv | (intros; apply GlobalTheory.CCRFock.polMap_comp_atPl_pderiv <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.fockHeisenbergOperatorOfCoords_eq_sum_mulLeft_pderiv : ∀ {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ),
    heisOp c = ∑ l : Ix P Q × Ix R S,
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c l.1 l.2) (lineSign l.1 l.2)) •
          LinearMap.mulLeft ℂ (MvPolynomial.X l) +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c l.1 l.2) (lineSign l.1 l.2)) •
          (MvPolynomial.pderiv l).toLinearMap) := by
  first | exact @GlobalTheory.CCRFock.heisOp_eq_sum_mul_pderiv | exact GlobalTheory.CCRFock.heisOp_eq_sum_mul_pderiv | (intros; apply GlobalTheory.CCRFock.heisOp_eq_sum_mul_pderiv <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.realLift_parity : GlobalTheory.RealLift.Parity := by
  first | exact @GlobalTheory.RealLift.even_im_hermitian_sub | exact GlobalTheory.RealLift.even_im_hermitian_sub | (intros; apply GlobalTheory.RealLift.even_im_hermitian_sub <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.oneParamSubgroup_generators_exist : GlobalTheory.RealLift.GenEx := by
  first | exact @GlobalTheory.RealLiftGen.genEx | exact GlobalTheory.RealLiftGen.genEx | (intros; apply GlobalTheory.RealLiftGen.genEx <;> assumption)
end

section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.fock_vacuum_pi_tensor_heisenberg_factorwise_signature : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ} (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ),
    sumPl (V := fun w : ι => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))))
      (PiTensorProduct.tprod ℂ fun _ => 1) =
    Complex.I • sumPl (V := fun w : ι => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ fun _ => 1) := by
  first | exact @GlobalTheory.FockVacD.sumPl_heisOp_vacuum_dep | exact GlobalTheory.FockVacD.sumPl_heisOp_vacuum_dep | (intros; apply GlobalTheory.FockVacD.sumPl_heisOp_vacuum_dep <;> assumption)
end
