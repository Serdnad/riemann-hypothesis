module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle159
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle154
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle184
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle221
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar

namespace GlobalTheory.TrueGeo.SmallSec

section Val

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z} {f g : Z.functionField}

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h, IsFractionRing.injective _ Z.functionField h.choose_spec]

theorem valAt_mul (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem regAt_pow {x : Z} (hf : RegAt x f) (n : ℕ) : RegAt x (f ^ n) := by
  obtain ⟨a, rfl⟩ := hf
  exact ⟨a ^ n, map_pow _ _ _⟩

theorem valAt_pow (hf : RegAt (below y) f) (n : ℕ) : valAt y (f ^ n) = valAt y f ^ n := by
  obtain ⟨a, rfl⟩ := hf
  rw [← map_pow, valAt_algebraMap, valAt_algebraMap, map_pow]

theorem valAt_ne_zero (hf : UnitAt (below y) f) : valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [valAt_algebraMap]
  exact (ha.map (Scheme.stalkClosedPointTo y).hom).ne_zero

theorem valAt_fnOf {U : Z.Opens} (hy : below y ∈ U) (h : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    valAt y (fnOf U h a) = valR y U a := by
  have e : fnOf U h a = algebraMap _ Z.functionField (Z.presheaf.germ U (below y) hy a) :=
    (algebraMap_germ hy a).symm
  have ht : ⊤ ≤ y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem y hy).ge
  have H := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y U hy)
  rw [e, valAt_algebraMap]
  first
  | rw [valR, dif_pos ht]
  refine H.trans ?_
  first
  | rfl

theorem ratVal_eq_valAt {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} (y : CxPts q σ)
    (hf : RegAt (under y) f) : ratVal f y = valAt y.1 f := by
  rw [ratVal, dif_pos hf]
  have he := hf.exists_fnOf.choose_spec.choose_spec.choose_spec
  conv_rhs => rw [← he]
  exact (valAt_fnOf hf.exists_fnOf.choose_spec.choose _ _).symm

end Val

section Fn

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
  (hη : j (genericPoint Y) ⤳ genericPoint X)

def fnMap : X.functionField →+* Y.functionField :=
  (X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)).hom

theorem fnMap_fnOf {U : X.Opens} (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ j ⁻¹ᵁ U)
    (s : Γ(X, U)) : fnMap j hη (fnOf U h s) = fnOf (j ⁻¹ᵁ U) h' (j.app U s) := by
  show (X.presheaf.germ U _ h ≫ X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)).hom s =
    (j.app U ≫ Y.presheaf.germ (j ⁻¹ᵁ U) (genericPoint Y) h').hom s
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

private theorem fnMap_algebraMap_eq_algebraMap_stalkMap (y : Y) (b : X.presheaf.stalk (j y)) :
    fnMap j hη (algebraMap _ X.functionField b) = algebraMap _ Y.functionField (j.stalkMap y b) := by
  have e1 := Scheme.Hom.stalkSpecializes_stalkMap_apply j (genericPoint Y) y
    ((genericPoint_spec Y).specializes trivial) b
  simp only [RingHom.algebraMap_toAlgebra, fnMap]
  rw [← e1]
  simp only [CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp_apply]

theorem exists_fnMap_eq [IsPreimmersion j] {y : Y} {u : Y.functionField}
    (hu : RegAt y u) : ∃ t, RegAt (j y) t ∧ fnMap j hη t = u := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := j.stalkMap_surjective y a
  exact ⟨algebraMap _ X.functionField b, ⟨b, rfl⟩, fnMap_algebraMap_eq_algebraMap_stalkMap j hη y b⟩

theorem fnMap_surjective [IsPreimmersion j] : Function.Surjective (fnMap j hη) := fun u =>
  let ⟨t, _, ht⟩ := exists_fnMap_eq j hη (regAt_genericPoint u)
  ⟨t, ht⟩

theorem regAt_fnMap_iff [IsPreimmersion j] {y : Y} {t : X.functionField} :
    RegAt y (fnMap j hη t) ↔ RegAt (j y) t := by
  constructor
  · intro h
    obtain ⟨t', ht', e⟩ := exists_fnMap_eq j hη h
    rwa [(fnMap j hη).injective e] at ht'
  · rintro ⟨b, rfl⟩
    exact ⟨_, (fnMap_algebraMap_eq_algebraMap_stalkMap j hη y b).symm⟩

theorem valAt_fnMap {K : Type} [Field K] (y : Sp K ⟶ Y) {t : X.functionField}
    (h : RegAt (j (below y)) t) : valAt y (fnMap j hη t) = valAt (y ≫ j) t := by
  obtain ⟨b, rfl⟩ := h
  rw [fnMap_algebraMap_eq_algebraMap_stalkMap, valAt_algebraMap]
  refine Eq.trans ?_ (valAt_algebraMap (y := y ≫ j) b).symm
  rw [Scheme.stalkClosedPointTo_comp]
  rfl

end Fn

section Model

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (M : Model Y)

theorem isPreimmersion_j : IsPreimmersion M.j := by
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  exact MorphismProperty.of_isPullback (P := @IsPreimmersion) M.pb.flip this

private theorem asIdeal_spMap_algebraMap_eq_bot (s : Sp F) : (spMap (algebraMap (𝓞 F) F) s).asIdeal = ⊥ := by
  haveI := s.isPrime
  have hs : s.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  have e : (spMap (algebraMap (𝓞 F) F) s).asIdeal = Ideal.comap (algebraMap (𝓞 F) F) s.asIdeal := by
    first
    | rfl
  rw [e, hs]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem mem_range_j {x : M.X} (hx : (M.p x).asIdeal = ⊥) : x ∈ Set.range M.j := by
  have e : M.p x = spMap (algebraMap (𝓞 F) F) (IsLocalRing.closedPoint F) :=
    PrimeSpectrum.ext (hx.trans (asIdeal_spMap_algebraMap_eq_bot _).symm)
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x _ e
  refine ⟨M.pb.isoPullback.inv z, ?_⟩
  rw [← hz1, ← M.pb.isoPullback_inv_fst]
  first
  | rfl

theorem asIdeal_p_j (y : Y.X) : (M.p (M.j y)).asIdeal = ⊥ := by
  have e : M.p (M.j y) = spMap (algebraMap (𝓞 F) F) (Y.str y) := by
    first
    | (show (M.j ≫ M.p) y = (Y.str ≫ spMap _) y
       rw [M.pb.w])
  rw [e, asIdeal_spMap_algebraMap_eq_bot]

theorem asIdeal_p_gen [IsIntegral M.X] : (M.p (genericPoint M.X)).asIdeal = ⊥ := by
  obtain ⟨y⟩ : Nonempty Y.X := inferInstance
  have hs : genericPoint M.X ⤳ M.j y := (genericPoint_spec M.X).specializes trivial
  have h3 : (M.p (genericPoint M.X)).asIdeal ≤ (M.p (M.j y)).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).2 (M.p.base.hom.map_specializes hs)
  rw [asIdeal_p_j] at h3
  exact le_bot_iff.1 h3

theorem j_gen_specializes [IsIntegral M.X] : M.j (genericPoint Y.X) ⤳ genericPoint M.X := by
  obtain ⟨y0, hy0⟩ := mem_range_j M (asIdeal_p_gen M)
  rw [← hy0]
  exact M.j.base.hom.map_specializes ((genericPoint_spec Y.X).specializes trivial)

end Model

end GlobalTheory.TrueGeo.SmallSec
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.RegCrit

theorem isUnit_of_one_le {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (c : e.O)
    (hc : 1 ≤ e.w c) : IsUnit c := by
  have h0 : (c : AlgebraicClosure F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact absurd hc (by norm_num)
  have h1 : (c : AlgebraicClosure F)⁻¹ ∈ e.O := by
    rw [e.mem_O, map_inv₀]
    exact inv_le_one_of_one_le₀ hc
  exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ h0))

end GlobalTheory.TrueGeo.RegCrit
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolExists

theorem exists_haar_prod {G H I : Type} [Fintype I] {U : I → Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G]
    [Group H] [TopologicalSpace H] [∀ i, Group (U i)] [∀ i, TopologicalSpace (U i)]
    [∀ i, IsTopologicalGroup (U i)] [∀ i, MeasurableSpace (U i)] [∀ i, BorelSpace (U i)]
    [∀ i, SecondCountableTopology (U i)] [∀ i, LocallyCompactSpace (U i)]
    (ν : ∀ i, Measure (U i)) [∀ i, (ν i).IsHaarMeasure] (e : G ≃ₜ* (∀ i, U i) × H) (K : Subgroup H)
    (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H)) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ B : ∀ i, Set (U i), (∀ i, MeasurableSet (B i)) →
      μ {h | (e h).2 ∈ K ∧ ∀ i, (e h).1 i ∈ B i} = ∏ i, ν i (B i) := by
  let j : H →* G := (e.symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj : Topology.IsEmbedding j :=
    e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkRight (1 : ∀ i, U i))
  haveI : IsTopologicalGroup H := hj.isInducing.topologicalGroup j
  haveI : SecondCountableTopology H := hj.secondCountableTopology
  haveI : T2Space H := hj.t2Space
  haveI : LocallyCompactSpace H :=
    hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds K.one_mem)
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  let K0 : TopologicalSpace.PositiveCompacts H :=
    ⟨⟨K, hKc⟩, by
      show (interior (K : Set H)).Nonempty
      rw [hKo.interior_eq]; exact ⟨1, K.one_mem⟩⟩
  let m : Measure ((∀ i, U i) × H) := (Measure.pi ν).prod (Measure.haarMeasure K0)
  haveI : m.IsHaarMeasure := inferInstanceAs (((Measure.pi ν).prod (Measure.haarMeasure K0)).IsHaarMeasure)
  refine ⟨m.map e.symm, e.symm.isHaarMeasure_map m, fun B hB => ?_⟩
  have hme : MeasurableEmbedding e.symm := e.symm.toHomeomorph.measurableEmbedding
  rw [hme.map_apply]
  have : e.symm ⁻¹' {h | (e h).2 ∈ K ∧ ∀ i, (e h).1 i ∈ B i} = (Set.univ.pi B) ×ˢ (K : Set H) := by
    ext x
    simp [and_comm]
  rw [this, Measure.prod_prod, Measure.pi_pi]
  have h1 : Measure.haarMeasure K0 (K : Set H) = 1 := Measure.haarMeasure_self
  rw [h1, mul_one]

theorem mat_mul {P Q : ℕ} (a b : UpqT P Q) : UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b := rfl

theorem mat_one {P Q : ℕ} : UpqT.mat (1 : UpqT P Q) = 1 := rfl

theorem exists_upq_mul {P Q M : ℕ} (A A' : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ)
    (B B' : Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ) (h1 : A * B = 1) (h2 : B * A = 1) (h3 : A' * B' = 1)
    (h4 : B' * A' = 1) (h : Aᴴ * Formalism.UG.Jpq P Q * A = A'ᴴ * Formalism.UG.Jpq P Q * A') :
    ∃ u : UpqT P Q, UpqT.mat u * A = A' := by
  let g : GL (Fin P ⊕ Fin Q) ℂ := ⟨A' * B, A * B',
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, h2, Matrix.one_mul, h3],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc B', h4, Matrix.one_mul, h1]⟩
  have hg : g ∈ Formalism.UG.Upq P Q := by
    show (A' * B)ᴴ * Formalism.UG.Jpq P Q * (A' * B) = Formalism.UG.Jpq P Q
    calc (A' * B)ᴴ * Formalism.UG.Jpq P Q * (A' * B) = Bᴴ * (A'ᴴ * Formalism.UG.Jpq P Q * A') * B := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (A * B)ᴴ * Formalism.UG.Jpq P Q * (A * B) := by
          rw [← h]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.UG.Jpq P Q := by rw [h1]; simp
  refine ⟨(⟨g, hg⟩ : Formalism.UG.Upq P Q), ?_⟩
  show A' * B * A = A'
  rw [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem exists_isVolMeasF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → ∃ μ, IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ := by
  intro F E _ _ _ _ _ _ cm I _ τ cd W hτ hW
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E cm
  have hθ := GlobalTheory.Mem.VolEmb.existsUnique_infEmb F E cm.sig hcm
  choose θ hθ1 hθ2 using fun i => hθ (τ i)
  have hA := fun i => GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (τ i))
  choose A hA1 using fun i => (hA i).2.1
  obtain ⟨e1, he1⟩ := GlobalTheory.T.unitaryGroup_realPoints_equiv_pi_indefiniteUnitary F E cm.sig W.rank W.gram I τ θ (fun ρ => (W.sig (τ ρ)).1)
    (fun ρ => (W.sig (τ ρ)).2) A hcm hτ hθ1 (fun i => hW (τ i)) hA1
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split F E cm.sig W.rank W.gram
  obtain ⟨L, hL, hLfg, hLsp⟩ := GlobalTheory.Mem.Vol.latC_full_lattice E W
  obtain ⟨K, hK, hKo, hKc⟩ := GlobalTheory.T.completedLattice_stabilizer_compact_open F E cm.sig W.rank W.gram L hLfg hLsp
  obtain ⟨-, hsc, ht2⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E cm.sig W.rank W.gram
  haveI : IsTopologicalGroup (HA (AF F) cm.sig W.gram) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (HA (AF F) cm.sig W.gram) := ⟨rfl⟩
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  have hinj := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective
  haveI := cd.haar
  let e : HA (AF F) cm.sig W.gram ≃ₜ*
      (∀ i, UpqT (W.sig (τ i)).1 (W.sig (τ i)).2) × HA (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) cm.sig W.gram :=
    e0.trans
      { e1.toMulEquiv.prodCongr (MulEquiv.refl _) with
        continuous_toFun := e1.continuous_toFun.prodMap continuous_id
        continuous_invFun := e1.continuous_invFun.prodMap continuous_id }
  have hee : ∀ h, e h = (e1 (e0 h).1, (e0 h).2) := fun h => rfl
  obtain ⟨μ, hμ, hμB⟩ := exists_haar_prod (fun i => cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2) e K hKo hKc
  refine ⟨μ, hμ, ⟨θ, hθ1⟩, fun θ' hθ' => ?_⟩
  obtain rfl : θ' = θ := funext fun i => hθ2 i _ (hθ' i)
  refine ⟨⟨A, hA1⟩, fun A' hA' B hB => ?_⟩
  have hu : ∀ i, ∃ u : UpqT (W.sig (τ i)).1 (W.sig (τ i)).2, UpqT.mat u * A i = A' i := by
    intro i
    obtain ⟨C, h1, h2⟩ := (hA i).2.2 _ (hA1 i)
    obtain ⟨C', h3, h4⟩ := (hA i).2.2 _ (hA' i)
    exact exists_upq_mul _ _ C C' h1 h2 h3 h4 ((hA1 i).trans (hA' i).symm)
  choose u hu using hu
  have key := hμB (fun i => (fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i))
    (fun i => measurable_const_mul _ (measurable_mul_const _ (hB i)))
  have hcj : ∀ i, cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2
      ((fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i)) =
      cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2 (B i) := by
    intro i
    haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant _ _ _ (cd.haar (W.sig (τ i)).1 (W.sig (τ i)).2)
    rw [measure_preimage_mul, measure_preimage_mul_right]
  rw [Finset.prod_congr rfl (fun i _ => hcj i)] at key
  rw [← key]
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, hee, Set.mem_preimage]
  rw [hK, (he0 h).1, hL]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  have h1 : UpqT.mat (e1 (e0 h).1 i) * A i = A i * infMat cm.sig W.gram (θ' i) h := by
    rw [he1, (he0 h).2]; rfl
  have h2 : UpqT.mat (u i * e1 (e0 h).1 i * (u i)⁻¹) * A' i = A' i * infMat cm.sig W.gram (θ' i) h := by
    have h3 : UpqT.mat (u i)⁻¹ * A' i = A i := by
      rw [← hu i, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mul]
    rw [mat_mul, mat_mul, Matrix.mul_assoc, h3, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, hu i]
  constructor
  · rintro ⟨b, hb, hbe⟩
    obtain ⟨C', h3, -⟩ := (hA i).2.2 _ (hA' i)
    have : b = u i * e1 (e0 h).1 i * (u i)⁻¹ := by
      apply hinj
      have h5 := congrArg (· * C') (hbe.trans h2.symm)
      simpa only [Matrix.mul_assoc, h3, Matrix.mul_one] using h5
    exact this ▸ hb
  · intro hb
    exact ⟨_, hb, h2⟩

end GlobalTheory.Mem.VolExists
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.GrassTopProd

theorem wt_add {ι : Type} (a b : ι × ℕ →₀ ℕ) :
    GlobalTheory.GrassTop.wt (a + b) = GlobalTheory.GrassTop.wt a + GlobalTheory.GrassTop.wt b := by
  unfold GlobalTheory.GrassTop.wt
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

theorem wt_sum {ι κ : Type} (s : Finset κ) (d : κ → ι × ℕ →₀ ℕ) :
    GlobalTheory.GrassTop.wt (∑ k ∈ s, d k) = ∑ k ∈ s, GlobalTheory.GrassTop.wt (d k) := by
  induction s using Finset.induction_on with
  | empty => simp [GlobalTheory.GrassTop.wt]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, wt_add, ih]

theorem wt_mapDomain {ι κ : Type} (f : ι × ℕ → κ × ℕ) (hf : ∀ x, (f x).2 = x.2) (d : ι × ℕ →₀ ℕ) :
    GlobalTheory.GrassTop.wt (d.mapDomain f) = GlobalTheory.GrassTop.wt d := by
  unfold GlobalTheory.GrassTop.wt
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
  simp [hf]

theorem adm_apply_prod_ren_eq_ite_mul_pointPoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ), (∀ τ, g τ ∈ GlobalTheory.GrassTop.basis Dw.p Dw.q) →
    ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ →
    Θ (∏ τ, GlobalTheory.GrassTop.ren τ (g τ)) = (if ∀ τ, g τ = X (true, Dw.p) ^ Dw.q then
      (-1 : ℝ) ^ (Dw.p * Dw.q * Fintype.card (GlobalTheory.AllWt.Psi H)) else 0) * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  intro E _ _ _ H Dw g hg Θ hΘ
  have hm : ∀ τ : GlobalTheory.AllWt.Psi H, Dw.mult τ.1 = Dw.p := fun τ => GlobalTheory.PointChern.mult_of_mem Dw τ.2
  split_ifs with hall
  · have h1 : ∏ τ, GlobalTheory.GrassTop.ren τ (g τ) = ∏ τ : GlobalTheory.AllWt.Psi H, X (τ.1, Dw.p) ^ Dw.q := by
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hall τ, map_pow]
      simp [GlobalTheory.GrassTop.ren, GlobalTheory.GrassTop.renVar]
    have h2 : GlobalTheory.LieBase.pointPoly H Dw = C ((-1 : ℝ) ^ (Dw.p * Dw.q * Fintype.card (GlobalTheory.AllWt.Psi H))) *
        ∏ τ : GlobalTheory.AllWt.Psi H, X (τ.1, Dw.p) ^ Dw.q := by
      unfold GlobalTheory.LieBase.pointPoly
      rw [Finset.prod_congr rfl (fun τ _ => by rw [hm τ])]
      rw [show Dw.p + Dw.q - Dw.p = Dw.q by omega]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← C_pow, ← pow_mul]
    rw [h1, h2, ← smul_eq_C_mul, LinearMap.map_smul, smul_eq_mul, ← mul_assoc, ← mul_pow]
    norm_num
  · push_neg at hall
    obtain ⟨σ, hσ⟩ := hall
    have key : ∀ τ, ∃ d : Bool × ℕ →₀ ℕ, GlobalTheory.GrassTop.wt d ≤ Dw.p * Dw.q ∧
        (g τ ≠ X (true, Dw.p) ^ Dw.q → GlobalTheory.GrassTop.wt d < Dw.p * Dw.q) ∧ g τ = monomial d 1 := by
      intro τ
      rcases hg τ with ⟨d, hd, he⟩ | he
      · exact ⟨d, hd.le, fun _ => hd, he⟩
      · refine ⟨Finsupp.single (true, Dw.p) Dw.q, ?_, fun h => absurd he h, ?_⟩
        · simp [GlobalTheory.GrassTop.wt, Finsupp.sum_single_index, mul_comm]
        · rw [he, X_pow_eq_monomial]
    choose d hd1 hd2 hd3 using key
    have hprod : ∏ τ, GlobalTheory.GrassTop.ren τ (g τ) =
        monomial (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) 1 := by
      rw [monomial_sum_one]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hd3 τ, GlobalTheory.GrassTop.ren, rename_monomial]
    have hw : GlobalTheory.GrassTop.wt (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) <
        Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) := by
      rw [wt_sum]
      calc ∑ τ, GlobalTheory.GrassTop.wt ((d τ).mapDomain (GlobalTheory.GrassTop.renVar τ))
          = ∑ τ, GlobalTheory.GrassTop.wt (d τ) :=
            Finset.sum_congr rfl fun τ _ => wt_mapDomain (GlobalTheory.GrassTop.renVar τ) (fun _ => rfl) (d τ)
        _ < ∑ _τ : GlobalTheory.AllWt.Psi H, Dw.p * Dw.q :=
            Finset.sum_lt_sum (fun τ _ => hd1 τ) ⟨σ, Finset.mem_univ _, hd2 σ hσ⟩
        _ = Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) := by simp
    have h0 : Θ (monomial (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) 1) = 0 :=
      hΘ.2.2.2 (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) hw.ne
    rw [hprod, h0, zero_mul]

end GlobalTheory.GrassTopProd
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteDimensional_smooth_irreducible_of_allPlus : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), AllPlus M → ∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧ ∀ U : Submodule ℂ (M.H τ), (∀ u : Matrix.unitaryGroup (Fin V.rank) ℂ, ∀ x ∈ U, M.σ τ u x ∈ U) → U = ⊥ ∨ U = ⊤ := by
  first | exact @GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible | exact GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible | (intros; apply GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y : Var F) (Eb : Fr (ratOf X) m 0) (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Reps Eb S φ f → ∀ (K : Type) [Field K] (w : Sp K ⟶ Y.X), ∃ A ∈ Eb.S ((w ≫ f) (IsLocalRing.closedPoint K)), ∃ h : Mat m K, Par 0 ⊤ h ∧ Bears S φ A h w := by
  first | exact @GlobalTheory.FlagBundle.bears_self | exact GlobalTheory.FlagBundle.bears_self | (intros; apply GlobalTheory.FlagBundle.bears_self <;> assumption)
end
