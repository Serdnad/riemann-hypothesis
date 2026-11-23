module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegreeEigenLatticeTensorRankOne
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasis
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle058
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle062
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle052
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle037
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle032
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle054
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem OntoAt.exists_eq_comp {S : Scheme.{0}} {I : Type} {B : I → Over S} {A A' : Over S} [GrpObj A] [GrpObj A']
    {φ : ∀ i, B i ⟶ A} {k : Type} [Field k] {t : Sp k ⟶ S} (hφ : OntoAt φ t) (Φ : A' ⟶ A) [IsMonHom Φ]
    (χ : ∀ i, B i ⟶ A') (e : ∀ i, χ i ≫ Φ = φ i) (y : Over.mk t ⟶ A) : ∃ x : Over.mk t ⟶ A', y = x ≫ Φ := by
  obtain ⟨n, i, x, rfl⟩ := hφ y
  refine ⟨(List.ofFn fun m => x m ≫ χ (i m)).prod, ?_⟩
  let F : (Over.mk t ⟶ A') →* (Over.mk t ⟶ A) :=
    MonoidHom.mk' (fun z => z ≫ Φ) fun z w => MonObj.mul_comp z w Φ
  change _ = F _
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext m
  simp [F, e]

theorem nonempty_isTen_of_isFam_top : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (σ : R →+* ℂ) (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (ψ : (⊤ : Submodule (𝓞 E) D.La) → (C.P.A ⟶ T.t.G)), Function.Injective σ → IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → IsFam C T h ⊤ ψ → OntoAt ψ (spMap σ) → Nonempty (IsTen C D h T) := by
  intro hL E _ _ _ H R _ _ _ σ ω C D ε h T ψ hσ hh hpos hfam honto
  obtain ⟨T₁, ⟨t⟩, -⟩ := GlobalTheory.T.exists_cm_tensor_lattice_curve_principal_triple hL E H R ω C D ε h hh hpos
  obtain ⟨Φ, hlin, htm, hlam⟩ := GlobalTheory.T.exists_tensorProduct_hom_of_cmCurveHomFamily E H R ω C D D ε h h T₁ T t ⊤ ψ
    (Submodule.topEquiv.symm : D.La ≃ₗ[𝓞 E] (⊤ : Submodule (𝓞 E) D.La)).toLinearMap 1 hh hh
    (fun a b => by rw [one_smul]; rfl) hfam
  rw [T₁.t.act.one] at hlam
  have hm : IsMonHom Φ := hlin.isMonHom
  have hsurj := (GlobalTheory.T.abelianScheme_surjective_of_onto_complex_points R σ hσ T.t.G T₁.t.G Φ T.ab T₁.ab
    (honto.exists_eq_comp Φ (fun a => t.ten.tmul a.1) fun a => htm a.1)).1
  have hred : IsReduced (Sp R) := inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  have hiso : IsIso Φ := GlobalTheory.T.isIso_of_surjective_principalPairing (Sp R) T₁.t.G T.t.G T₁.t.PP.L T.t.PP.L Φ T₁.ab T.ab T₁.t.PP.isLB T.t.PP.isLB hm
    T₁.ktriv hlam hsurj
  have key : ∀ a, (t.ten.ofIso (b' := Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) (asIso Φ)
      ⟨hm, fun c => hlin.comm _⟩).tmul a = ψ ⟨a, trivial⟩ := fun a => htm a
  refine ⟨⟨t.ten.ofIso (asIso Φ) ⟨hm, fun c => hlin.comm _⟩, fun s a => ?_, fun a b => ?_⟩⟩
  · rw [key, key]
    exact hfam.2.2.1 s ⟨a, trivial⟩
  · rw [key, key]
    exact hfam.2.2.2 ⟨a, trivial⟩ ⟨b, trivial⟩

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.two_mul_degree_eigenLattice_tensor_rankOne : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ω : 𝓞 K) (C : Ell H (𝓞 K) ω) (D : Datum H) (ε : ℤˣ) (hK : D.La → D.La → OK H) (T : PAT H (Sp (𝓞 K))) (x : ℝ), Splits E K → D.p + D.q = 1 → IsKForm D ε hK → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → Nonempty (IsTen C D hK T) → C.HasPeriod x → ∀ (F : GenFib T.pol) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.w0 = ω → 2 * deg h (F.eigLat T.t.act τ) = x + Real.log H.d / 2 - Real.log (NumberField.rootDiscr E) := by
  first | exact @GlobalTheory.CM.TensorDeg.two_mul_deg_eigLat | exact GlobalTheory.CM.TensorDeg.two_mul_deg_eigLat | (intros; apply GlobalTheory.CM.TensorDeg.two_mul_deg_eigLat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → letI := (iK.comp (algebraMap c.F z.K)).toAlgebra; ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr) (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (a : T.Fr), φ.toRingHom = iK → FrMap φ z.y yT → FrChg g a yT y' → (∀ b, IsUnit (g b).det) → LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u → ∀ (b : E →+* ℂ) (j k : Fin (Dw.mult b)) (cl : z.K), IsLocGen p cl (z.ℓ (z.e ⟨b, j⟩)).I → iK cl * (g b)⁻¹ j k ∈ Set.range (algebraMap T.V T.Fr) := by
  first | exact @GlobalTheory.LamT.LetterInt.letter_integral_in_eigenbasis | exact GlobalTheory.LamT.LetterInt.letter_integral_in_eigenbasis | (intros; apply GlobalTheory.LamT.LetterInt.letter_integral_in_eigenbasis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.FibIndep

section Lattice

variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']


open scoped ComplexOrder in
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] in
theorem injective_of_isometry (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V')
    (hM : ∀ s c c', h'.form s (M c) (M c') = h.form s c c') : Function.Injective M := by
  obtain ⟨s⟩ : Nonempty (K →+* ℂ) := inferInstance
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  by_contra hne
  have hli : LinearIndependent K ![c] := (linearIndependent_unique_iff (v := ![c])).2 (by simpa using hne)
  have hpos := (h.posDef s 1 ![c] hli).diag_pos (i := 0)
  have hzero : h'.form s 0 0 = 0 := by simpa using h'.smul_right s 0 0 0
  have hcc : h.form s c c = 0 := by rw [← hM, hc, hzero]
  simp only [Matrix.of_apply, Matrix.cons_val_fin_one] at hpos
  rw [hcc] at hpos
  exact lt_irrefl _ hpos

theorem deg_map_of_isometry (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V')
    (hM : ∀ s c c', h'.form s (M c) (M c') = h.form s c c') {E : Submodule (𝓞 K) V} (hE : E.FG) :
    deg h E = deg h' (E.map (M.restrictScalars (𝓞 K))) := by
  have hinj := injective_of_isometry h h' M hM
  obtain ⟨v, hv⟩ := exists_isFrame E hE
  obtain ⟨hvE, hvli, hvsp⟩ := hv
  have hv' : IsFrame K (E.map (M.restrictScalars (𝓞 K))) (M ∘ v) := by
    refine ⟨fun i => Submodule.mem_map_of_mem (hvE i), hvli.map' M (LinearMap.ker_eq_bot.2 hinj), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hvsp hx
    rw [Set.range_comp, Submodule.span_image]
    exact Submodule.mem_map_of_mem hx'
  rw [arakelovDegree_eq_degreeOfFamily h hE ⟨hvE, hvli, hvsp⟩, arakelovDegree_eq_degreeOfFamily h' (hE.map _) hv']
  have hgram : ∀ σ, h'.gram σ (M ∘ v) = h.gram σ v := fun σ => by
    ext i j
    simp [HermFam.gram, hM]
  have hspan : Submodule.span (𝓞 K) (Set.range (M ∘ v)) =
      (Submodule.span (𝓞 K) (Set.range v)).map (M.restrictScalars (𝓞 K)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hidx : (Submodule.span (𝓞 K) (Set.range (M ∘ v))).toAddSubgroup.relIndex
      (E.map (M.restrictScalars (𝓞 K))).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup := by
    rw [hspan, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  unfold degreeOfFamily
  rw [hidx]
  simp only [hgram]

end Lattice

variable {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp (𝓞 K))}

theorem existsUnique_coord (F : GenFib P) {u : epsR (𝓞 K) ⟶ P.A} (hu : IsTangent u) : ∃! c, F.IsCoord u c := by
  have hb := F.basis
  unfold IsLieBasis at hb
  have hf := F.fib
  unfold IsPolFibre at hf
  obtain ⟨-, hpb, -⟩ := hf
  obtain ⟨w, hw, hwu⟩ := existsUnique_isVecOver hpb.1 u
  obtain ⟨c, hc, hcu⟩ := hb.2 w (hw.isTangent hpb hu)
  refine ⟨c, ⟨hu, w, hw, hc⟩, ?_⟩
  rintro c' ⟨-, w', hw', hc'⟩
  obtain rfl := hwu w' hw'
  exact hcu c' hc'

theorem image_coord (F F' : GenFib P) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)} (hM : F.IsDiffOf F' (𝟙 P.A) M)
    (p : (epsR (𝓞 K) ⟶ P.A) → Prop) :
    Submodule.span (𝓞 K) {c | ∃ u, F'.IsCoord u c ∧ p u} =
      (Submodule.span (𝓞 K) {c | ∃ u, F.IsCoord u c ∧ p u}).map (M.restrictScalars (𝓞 K)) := by
  rw [Submodule.map_span]
  congr 1
  ext c
  constructor
  · rintro ⟨u, hu, hp⟩
    obtain ⟨ht, -⟩ := id hu
    obtain ⟨c₀, hc₀, -⟩ := existsUnique_coord F ht
    refine ⟨c₀, ⟨u, hc₀, hp⟩, ?_⟩
    have h1 := hM u c₀ hc₀
    rw [Category.comp_id] at h1
    exact (existsUnique_coord F' ht).unique h1 hu
  · rintro ⟨c₀, ⟨u, hu, hp⟩, rfl⟩
    have h1 := hM u c₀ hu
    rw [Category.comp_id] at h1
    exact ⟨u, h1, hp⟩

theorem deg_lieLat_eq : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P) (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → deg h F.lieLat = deg h' F'.lieLat ∧ ∀ (O : Type) [CommRing O] (act : OAct O P.A) (τ : O →+* 𝓞 K), deg h (F.eigLat act τ) = deg h' (F'.eigLat act τ) := by
  intro hU hL K _ _ P F F' h h' hh hh'
  obtain ⟨⟨M, hM, -⟩, -⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P F' (𝟙 P.A) inferInstance
  have hN : F.IsDiffOf F (𝟙 P.A) LinearMap.id := fun u c hc => by
    rw [Category.comp_id]
    exact hc
  have hlam : LamEq P.L (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) :=
    GlobalTheory.PolBaseChange.lbIso_refl (GlobalTheory.LamCalc.cubeLB_isLB P.isLB _)
  have hiso : ∀ s c c', h'.form s (M c) (M c') = h.form s c c' := fun s c c' => by
    simpa using GlobalTheory.T.hermitianMetric_differential_eq_of_pairing_relation hU hL K P F P F' h h' (𝟙 P.A) (𝟙 P.A) M LinearMap.id hh hh'
      inferInstance inferInstance hlam hM hN s c c'
  have hFG := (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K P F).1
  refine ⟨?_, fun O _ act τ => ?_⟩
  · have e := image_coord F F' hM (fun _ => True)
    simp only [and_true] at e
    have e' : F'.lieLat = F.lieLat.map (M.restrictScalars (𝓞 K)) := e
    rw [e']
    exact deg_map_of_isometry h h' M hiso hFG
  · have e := image_coord F F' hM (fun u => ∀ a, IsLieComb ![τ a] ![u] (u ≫ act.act a))
    have hle : F.eigLat act τ ≤ F.lieLat :=
      Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩
    have hFG' : (F.eigLat act τ).FG := hFG.of_le hle
    have e' : F'.eigLat act τ = (F.eigLat act τ).map (M.restrictScalars (𝓞 K)) := e
    rw [e']
    exact deg_map_of_isometry h h' M hiso hFG'

end GlobalTheory.FibIndep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.LamF


open IntCoord in
theorem diff_mem_eigLat {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {O : Type} [CommRing O] {a : OAct O P.A} {a' : OAct O P'.A} {f : P.A ⟶ P'.A}
    (hf : ∀ x, a.act x ≫ f = f ≫ a'.act x) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    (hM : F.IsDiffOf F' f M) (τ : O →+* 𝓞 K) {c : Fin F.P₀.g → K} (hc : c ∈ F.eigLat a τ) :
    M c ∈ F'.eigLat a' τ := by
  obtain ⟨u, hu, he⟩ := ((integral_tangent_coordinates K P F).2.2.2.2.2 O a τ c).1 hc
  refine Submodule.subset_span ⟨u ≫ f, hM u c hu, fun x => ?_⟩
  rw [isLieComb_one_iff, Category.assoc, ← hf, ← Category.assoc, (isLieComb_one_iff _ _ _).1 (he x),
    Category.assoc]

theorem map_eigLat_of_iso {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {O : Type} [CommRing O] {a : OAct O P.A} {a' : OAct O P'.A} (e : P.A ≅ P'.A)
    (hf : ∀ x, a.act x ≫ e.hom = e.hom ≫ a'.act x) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    {M' : (Fin F'.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)}
    (hM : F.IsDiffOf F' e.hom M) (hM' : F'.IsDiffOf F e.inv M') (τ : O →+* 𝓞 K) :
    (F.eigLat a τ).map (M.restrictScalars (𝓞 K)) = F'.eigLat a' τ := by
  refine le_antisymm ?_ fun c hc => ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact diff_mem_eigLat hf hM τ hc
  · have hf' : ∀ x, a'.act x ≫ e.inv = e.inv ≫ a.act x := fun x => by
      rw [Iso.comp_inv_eq, Category.assoc, hf, Iso.inv_hom_id_assoc]
    refine ⟨M' c, diff_mem_eigLat hf' hM' τ hc, ?_⟩
    obtain ⟨u, hu, -⟩ := ((integral_tangent_coordinates K P' F').2.2.2.2.2 O a' τ c).1 hc
    have h2 := hM _ _ (hM' _ _ hu)
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h2
    exact ((integral_tangent_coordinates K P' F').1 u hu.1).unique h2 hu

theorem deg_eigLat_eq_of_iso : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P P' : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (O : Type) [CommRing O] (a : OAct O P.A) (a' : OAct O P'.A) (e : P.A ≅ P'.A), F.IsHerm h → F'.IsHerm h' → Serre.IsLinearHom a a' e.hom → LamEq P'.L e.hom e.hom P.L (𝟙 P.A) (𝟙 P.A) → ∀ τ : O →+* 𝓞 K, deg h (F.eigLat a τ) = deg h' (F'.eigLat a' τ) := by
  intro hT hL K _ _ P P' F F' h h' O _ a a' e hh hh' hlin hlam τ
  have hm : IsMonHom e.hom := hlin.1
  have hm' : IsMonHom e.inv := inferInstance
  obtain ⟨M, hM, -⟩ := (GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' e.hom hm).1
  obtain ⟨M', hM', -⟩ := (GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P' F' P F e.inv hm').1
  have hid : F.IsDiffOf F (𝟙 P.A) LinearMap.id := fun u c hu => by simpa using hu
  have hiso := GlobalTheory.T.hermitianMetric_differential_eq_of_pairing_relation hT hL K P F P' F' h h' e.hom (𝟙 P.A) M LinearMap.id hh hh' hm inferInstance hlam hM hid
  have hle : F.eigLat a τ ≤ F.lieLat := Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩
  have hfg : (F.eigLat a τ).FG := (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K P F).1.of_le hle
  rw [← map_eigLat_of_iso e hlin.2 hM hM' τ]
  exact (deg_map_isometry K _ _ h h' M _ hfg hiso).symm

end GlobalTheory.LamF
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.LenOne

theorem re_form_smul_le {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] (h : HermFam K V)
    (s : K →+* ℂ) (t : K) {x : V} (hx : x ≠ 0) : (h.form s x (t • x)).re ≤ ‖s t‖ * (h.form s x x).re := by
  have hp := (h.posDef s 1 ![x] (by simpa [linearIndependent_unique_iff] using hx)).diag_pos (i := 0)
  have hp' : 0 < h.form s x x := by simpa using hp
  obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hp'
  rw [h.smul_right, Complex.mul_re, ← h2, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_right (Complex.re_le_norm _) h1.le

theorem diff_single_eq {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} (F : GenFib P)
    (F' : GenFib P') {f : P.A ⟶ P'.A} {f₀ : F.P₀.A ⟶ F'.P₀.A} (e : f₀.left ≫ F'.φ = F.φ ≫ f.left)
    {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    (hM : ∀ c w, IsLieComb c F.v w → IsLieComb (M c) F'.v (w ≫ f₀)) (i : Fin F.P₀.g) {U : Fin F'.P₀.g → K}
    {w : epsR K ⟶ F'.P₀.A} (hU : IsLieComb U F'.v w) (hw : w.left ≫ F'.φ = (F.v i).left ≫ F.φ ≫ f.left) :
    M (Pi.single i 1) = U := by
  have := F.P₀.isAb.comm
  have := F'.P₀.isAb.comm
  obtain rfl : w = F.v i ≫ f₀ := Over.OverMorphism.ext (F'.fib.2.1.1.hom_ext
    (by rw [hw, Over.comp_left, Category.assoc, e]) ((Over.w _).trans (Over.w _).symm))
  exact (F'.basis.2 _ ((LieComb.lieComb_algebra K _ _ F'.v F'.basis.1).2.1 U _ hU)).unique
    (hM _ _ ((LieComb.lieComb_algebra K _ _ F.v F.basis.1).2.2.2.1 i)) hU

theorem form_image_le : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P P' : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A), F.IsHerm h → F'.IsHerm h' → IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → ∀ (i : Fin F.P₀.g) (t : K) (w : epsR K ⟶ F.P₀.A) (U : Fin F'.P₀.g → K) (w' : epsR K ⟶ F'.P₀.A), IsLieComb (Pi.single i t) F.v w → (F.v i).left ≫ F.φ ≫ g.left = w.left ≫ F.φ → IsLieComb U F'.v w' → w'.left ≫ F'.φ = (F.v i).left ≫ F.φ ≫ f.left → ∀ s : K →+* ℂ, (h'.form s U U).re ≤ ‖s t‖ * (h.form s (Pi.single i 1) (Pi.single i 1)).re := by
  intro hT hL K _ _ P P' F F' h h' f g hh hh' hf hg hlam i t w U w' hw ew hU ew' s
  obtain ⟨⟨M, hM, -⟩, f₀, -, ef, hf₀⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f hf
  obtain ⟨⟨N, hN, -⟩, g₀, -, eg, hg₀⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P F g hg
  have h1 := diff_single_eq F F' ef (hf₀ M hM) i hU ew'
  have h2 := diff_single_eq F F eg (hg₀ N hN) i hw ew.symm
  have h3 := GlobalTheory.T.hermitianMetric_differential_eq_of_pairing_relation hT hL K P F P' F' h h' f g M N hh hh' hf hg hlam hM hN s (Pi.single i 1) (Pi.single i 1)
  have h4 : (Pi.single i t : Fin F.P₀.g → K) = t • (Pi.single i 1 : Fin F.P₀.g → K) := by
    rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [h1, h2, h4] at h3
  rw [h3]
  exact re_form_smul_le h s t (by simp)

end GlobalTheory.LamF.LenOne
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (T : PAT H (Sp (𝓞 K))) (F : GenFib T.pol) (p q : ℕ), Splits E K → HasType H T.t.act ρ p q → ρ ^ 2 = -(H.d : 𝓞 K) → (∀ τ : 𝓞 E →+* 𝓞 K, latRank K (F.eigLat T.t.act τ) = open Classical in if τ H.rt = ρ then p else q) ∧ iSupIndep (fun τ : 𝓞 E →+* 𝓞 K => Submodule.span K (F.eigLat T.t.act τ : Set (Fin F.P₀.g → K))) ∧ ⨆ τ : 𝓞 E →+* 𝓞 K, Submodule.span K (F.eigLat T.t.act τ : Set (Fin F.P₀.g → K)) = ⊤ ∧ T.g = Module.finrank ℚ E / 2 * (p + q) ∧ Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = ρ} = Module.finrank ℚ E / 2 ∧ Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = -ρ} = Module.finrank ℚ E / 2 := by
  first | exact @GlobalTheory.CM.EigDec.eigen_decomposition | exact GlobalTheory.CM.EigDec.eigen_decomposition | (intros; apply GlobalTheory.CM.EigDec.eigen_decomposition <;> assumption)
end
