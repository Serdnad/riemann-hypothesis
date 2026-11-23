module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle457
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle458
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle003
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.InertJacobiLevels.Bundle001
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.GeoFW

open GlobalTheory.Mem.R3.Rw

variable {LL LL' Ks : Type} [Field LL] [Field LL'] [Field Ks] [Algebra Ks LL] [Algebra Ks LL']

def crdMap (ι : LL →+* LL') {n n' : ℕ} (hn : n = n') (x : Fin n → LL) : Fin n' → LL' := fun k' => ι (x (Fin.cast hn.symm k'))

theorem crdOver_crdMap (ι : LL →+* LL') {n n' : ℕ} (hn : n = n') (x : Fin n → LL) : CrdOver ι x (crdMap ι hn x) :=
  ⟨hn, fun k k' hk => by
    unfold crdMap
    congr 2
    exact Fin.ext (by simp [hk])⟩

theorem crdMap_eq_of_crdOver (ι : LL →+* LL') {n n' : ℕ} (hn : n = n') {x : Fin n → LL} {x' : Fin n' → LL'}
    (h : CrdOver ι x x') : crdMap ι hn x = x' := by
  funext k'
  exact (h.2 (Fin.cast hn.symm k') k' rfl).symm

def crdLin (ι : LL →+* LL') (hι : ∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) {n n' : ℕ} (hn : n = n') :
    (Fin n → LL) →ₗ[Ks] (Fin n' → LL') where
  toFun := crdMap ι hn
  map_add' x y := by funext k; simp [crdMap]
  map_smul' c x := by funext k; simp [crdMap, Algebra.smul_def, hι]

theorem crdMap_injective (ι : LL →+* LL') {n n' : ℕ} (hn : n = n') : Function.Injective (crdMap ι hn) := by
  intro x y h
  funext k
  have := congrFun h (Fin.cast hn k)
  simp only [crdMap, Fin.cast_cast, Fin.cast_eq_self] at this
  exact ι.injective this

def baseChangeEquiv (ι : LL →+* LL') (hι : ∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) {n n' : ℕ} (hn : n = n')
    (WK : Submodule Ks (Fin n → LL)) (WK' : Submodule Ks (Fin n' → LL'))
    (hmem : ∀ x x', CrdOver ι x x' → (x' ∈ WK' ↔ x ∈ WK)) (honto : ∀ x' ∈ WK', ∃ x : Fin n → LL, CrdOver ι x x') : WK ≃ₗ[Ks] WK' :=
  LinearEquiv.ofBijective
    (((crdLin ι hι hn).comp WK.subtype).codRestrict WK' fun x => (hmem _ _ (crdOver_crdMap ι hn x.1)).2 x.2)
    ⟨fun x y h => Subtype.ext (crdMap_injective ι hn (congrArg Subtype.val h)), fun x' => by
      obtain ⟨x, hx⟩ := honto x'.1 x'.2
      exact ⟨⟨x, (hmem _ _ hx).1 x'.2⟩, Subtype.ext (crdMap_eq_of_crdOver ι hn hx)⟩⟩

theorem baseChangeEquiv_crdOver (ι : LL →+* LL') (hι : ∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) {n n' : ℕ}
    (hn : n = n') (WK : Submodule Ks (Fin n → LL)) (WK' : Submodule Ks (Fin n' → LL'))
    (hmem : ∀ x x', CrdOver ι x x' → (x' ∈ WK' ↔ x ∈ WK)) (honto : ∀ x' ∈ WK', ∃ x : Fin n → LL, CrdOver ι x x') (x : WK) :
    CrdOver ι x.1 (baseChangeEquiv ι hι hn WK WK' hmem honto x).1 :=
  crdOver_crdMap ι hn x.1

end GlobalTheory.Mem.R3.Rw.GeoFW

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo

namespace GlobalTheory

theorem ksForm_baseChange_crd {LL LL' Ks : Type} [Field LL] [Field LL'] [Field Ks] [Algebra Ks LL] [Algebra Ks LL']
    (ι : LL →+* LL') (hι : ∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) {n n' : ℕ} (hn : n = n')
    (WK : Submodule Ks (Fin n → LL)) (WK' : Submodule Ks (Fin n' → LL'))
    (hmem : ∀ x x', GlobalTheory.Mem.R3.Rw.CrdOver ι x x' → (x' ∈ WK' ↔ x ∈ WK))
    (honto : ∀ x' ∈ WK', ∃ x : Fin n → LL, GlobalTheory.Mem.R3.Rw.CrdOver ι x x')
    (h : ∃ (m : ℕ) (b : Fin m → (Fin n → LL)), (∀ i, b i ∈ WK) ∧ LinearIndependent Ks b ∧
        Submodule.span Ks (Set.range b) = WK ∧ LinearIndependent LL b ∧
        Submodule.span LL (Set.range b) = ⊤) :
    ∃ (m : ℕ) (b : Fin m → (Fin n' → LL')), (∀ i, b i ∈ WK') ∧ LinearIndependent Ks b ∧
        Submodule.span Ks (Set.range b) = WK' ∧ LinearIndependent LL' b ∧
        Submodule.span LL' (Set.range b) = ⊤ := by
  subst hn
  have hc : ∀ x : Fin n → LL, GlobalTheory.Mem.R3.Rw.CrdOver ι x (fun k => ι (x k)) :=
    fun x => ⟨rfl, fun k k' hk => by rw [Fin.ext hk]⟩
  refine GlobalTheory.ksForm_baseChange ι hι WK WK' (fun x => (hmem x _ (hc x)).symm) ?_ h
  intro x' hx'
  obtain ⟨x, -, hx⟩ := honto x' hx'
  have he : x' = fun k => ι (x k) := funext fun k => hx k k rfl
  subst he
  exact ⟨x, (hmem x _ (hc x)).1 hx', rfl⟩

end GlobalTheory



theorem GlobalTheory.ksForm_moved : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
    B'.toPre = B.toPre → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt) (hX' : B'.fields.Ok)
    (Wt' : Set B'.places.Pl) (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
    (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
    (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
    Formalism.L2.Pj.LawsCore core'.toCore →
    letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
      (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F),
      RSideW z Wt' R' → HEq R'.toLevCh.mu0 z.R.toLevCh.mu0 →
      ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
      ∀ i : Fin (w'.st Z').toD7.R.m, (R'.FW i).IsKsForm := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hR hmu ι hι i
  obtain ⟨P'⟩ := B'
  dsimp only at hPre
  subst hPre
  rcases core' with ⟨⟨⟨H', l', c'⟩⟩⟩
  obtain ⟨hH, hl, hc, -⟩ := hcore
  have hH' := eq_of_heq hH
  subst hH'
  have hl' := eq_of_heq hl
  subst hl'
  have hc' := eq_of_heq hc
  subst hc'
  obtain ⟨-, -, -, -, -, hnW, -, -, -, -, -, -, hcol, -⟩ := hR
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hι'⟩ := hcol i i rfl
  obtain ⟨-, ⟨hmem, honto⟩, -⟩ := hι' ι hι
  have hn : z.R.nW i = R'.nW i := congrFun (eq_of_heq hnW).symm i
  have halg2 : ∀ y : ↥z.core.Q.c.F, ι (algebraMap _ _ y) = @algebraMap _ _ _ _ alg' y := by
    intro y
    apply (w'.st Z').toD7.what₂.embLL.injective
    rw [hι]
    exact (z.alg_eq y).trans (halg y).symm
  exact GlobalTheory.ksForm_baseChange_crd ι halg2 hn (z.R.FW i).WK (R'.FW i).WK hmem honto (z.geo.fw.ks i)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Top.KerGlob

theorem weak_approx {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (w : ι → HeightOneSpectrum (𝓞 F)) (hw : Function.Injective w) (y : ∀ i, (w i).adicCompletion F) (c : F) (hc : c ≠ 0) :
    ∃ a : F, ∀ i, Valued.v (algebraMap F ((w i).adicCompletion F) a - y i) ≤
      Valued.v (algebraMap F ((w i).adicCompletion F) c) :=
  GlobalTheory.T.exists_approx_finite_places_numberField w hw y c hc

theorem matrix_approx {ι : Type} [Fintype ι] [DecidableEq ι] (W Q : ι → Type) [∀ q, CommRing (W q)] [∀ q, IsDomain (W q)]
    [∀ q, IsDiscreteValuationRing (W q)] [∀ q, Field (Q q)] [∀ q, Algebra (W q) (Q q)] [∀ q, IsFractionRing (W q) (Q q)]
    {F : Type} [Field F] (f : ∀ q, F →+* Q q) (π : ∀ q, W q) (hπ : ∀ q, Irreducible (π q)) (t : F)
    (ht : ∀ q, f q t = algebraMap (W q) (Q q) (π q))
    (hd : ∀ (y : ∀ q, W q) (N : ℕ), ∃ x : F, ∀ q, ∃ z : W q, f q x = algebraMap (W q) (Q q) (y q + π q ^ N * z))
    {n : ℕ} (g : ∀ q, Matrix (Fin n) (Fin n) (Q q)) (hg : ∀ q, IsUnit (g q).det) (q0 : ι) :
    ∃ (B : Matrix (Fin n) (Fin n) F) (u : Matrix (Fin n) (Fin n) (W q0)), IsUnit u.det ∧
      B.map (f q0) = g q0 * u.map (algebraMap (W q0) (Q q0)) ∧
      ∀ q, q ≠ q0 → ∀ c, (fun i => f q (B i c)) ∈ Formalism.MainNotions.G.colSpan (W q) (g q) :=
  GlobalTheory.T.exists_global_matrix_approximation_mod_integral W Q f π hπ t ht hd g hg q0

theorem colSpan_mul_le {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (g : Matrix (Fin k) (Fin k) K)
    (u : Matrix (Fin k) (Fin k) R) :
    Formalism.MainNotions.G.colSpan R (g * u.map (algebraMap R K)) ≤ Formalism.MainNotions.G.colSpan R g := by
  rw [Formalism.MainNotions.G.colSpan, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have : (fun i => (g * u.map (algebraMap R K)) i c) = ∑ j, u j c • fun i => g i j := by
    funext i
    simp [Matrix.mul_apply, Algebra.smul_def, mul_comm]
  change (fun i => (g * u.map (algebraMap R K)) i c) ∈ Formalism.MainNotions.G.colSpan R g
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem colSpan_mul_eq {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (g : Matrix (Fin k) (Fin k) K)
    (u : Matrix (Fin k) (Fin k) R) (hu : IsUnit u.det) :
    Formalism.MainNotions.G.colSpan R (g * u.map (algebraMap R K)) = Formalism.MainNotions.G.colSpan R g := by
  refine le_antisymm (colSpan_mul_le g u) ?_
  have := colSpan_mul_le (g * u.map (algebraMap R K)) u⁻¹
  rwa [Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this

theorem map_int {F E : Type} [Field F] [NumberField F] [Field E] (w : HeightOneSpectrum (𝓞 F))
    (φ : E →+* w.adicCompletion F) (x : 𝓞 E) : φ x ∈ w.adicCompletionIntegers F := by
  have h2 : IsIntegral (w.adicCompletionIntegers F) (φ x) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) φ (RingHom.ext_int _ _) x.isIntegral_coe
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w.adicCompletionIntegers F)
    (K := w.adicCompletion F)).1 h2
  rw [← hy]
  exact y.2

theorem step {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {W Q : Type} [CommRing W] [Field Q]
    [Algebra W Q] (e : Q ≃+* w.adicCompletion F)
    (heW : ∀ x, x ∈ Set.range (algebraMap W Q) ↔ e x ∈ w.adicCompletionIntegers F) (p N : ℕ) (hp : (p : F) ≠ 0)
    (a : F) (y : W)
    (hv : Valued.v (algebraMap F (w.adicCompletion F) a - e (algebraMap W Q y)) ≤
      Valued.v (algebraMap F (w.adicCompletion F) ((p : F) ^ N))) :
    ∃ z : W, e.symm (algebraMap F (w.adicCompletion F) a) = algebraMap W Q (y + (p : W) ^ N * z) := by
  have hcc0 : algebraMap F (w.adicCompletion F) ((p : F) ^ N) ≠ 0 := (map_ne_zero _).2 (pow_ne_zero _ hp)
  have hz' : (algebraMap F (w.adicCompletion F) a - e (algebraMap W Q y)) / algebraMap F (w.adicCompletion F) ((p : F) ^ N) ∈
      w.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    exact div_le_one_of_le₀ hv zero_le
  obtain ⟨z, hz⟩ := (heW (e.symm _)).2 (by rw [e.apply_symm_apply]; exact hz')
  refine ⟨z, ?_⟩
  apply e.injective
  rw [e.apply_symm_apply, map_add (f := _), map_add (f := _), map_mul, hz, map_mul, e.apply_symm_apply, map_pow, map_pow, map_natCast,
    map_natCast]
  have hcc' : algebraMap F (w.adicCompletion F) ((p : F) ^ N) = (p : w.adicCompletion F) ^ N := by
    rw [map_pow, map_natCast]
  rw [← hcc', mul_div_cancel₀ _ hcc0]
  ring

variable {D : D7} {H : Formalism.L2.Herm.HermColsCh D} (Gs : Formalism.L2.Herm.SymmetricGroupCompatibility D H) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v))

theorem splitPlaceEmbedding_integers_mem_localIntegers (q : Fin (D.gat u v hg).P.nV) (r : 𝓞 D.host.E) :
    KerOne.iw0 Gs u v hg q (algebraMap (𝓞 D.host.E) D.host.E r) ∈
      Set.range (algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q)) := by
  refine ((Gs u v hg).completion_integers_iff q _ rfl _).2 ?_
  rw [KerOne.splitPlaceIdempotent_cmEmbedding_compat]
  exact map_int _ (((RingHom.fst _ _).comp ((Gs u v hg).spl _ ((Gs u v hg).pl q).2).toRingHom).comp
      (Formalism.UG.inclE (F := D.host.F) ((((Gs u v hg).pl q).1).adicCompletion D.host.F))) r

theorem splitPlaceEmbedding_baseField_eq_completion (q : Fin (D.gat u v hg).P.nV) (a : D.host.F) :
    KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E a) =
      ((Gs u v hg).eQ q _ rfl).symm (algebraMap D.host.F ((((Gs u v hg).pl q).1).adicCompletion D.host.F) a) := by
  apply ((Gs u v hg).eQ q _ rfl).injective
  rw [KerOne.splitPlaceIdempotent_cmEmbedding_compat]
  refine ((Gs u v hg).spl_F _ _ a).trans ?_
  exact (RingEquiv.apply_symm_apply _ _).symm

theorem pl_inj : Function.Injective (fun q : Fin (D.gat u v hg).P.nV => ((Gs u v hg).pl q).1) :=
  fun _ _ h => (Gs u v hg).pl.injective (Subtype.ext h)

theorem dense (y : ∀ q, (D.gat u v hg).P.W q) (N : ℕ) : ∃ x : D.host.F, ∀ q, ∃ z : (D.gat u v hg).P.W q,
    KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E x) =
      algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q)
        (y q + ((D.what₂.places.resChar v : ℕ) : (D.gat u v hg).P.W q) ^ N * z) := by
  rcases isEmpty_or_nonempty (Fin (D.gat u v hg).P.nV) with h | ⟨⟨q1⟩⟩
  · exact ⟨0, fun q => (IsEmpty.false q).elim⟩
  have hp0 : ((D.what₂.places.resChar v : ℕ) : D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (((D.gat u v hg).P.setting q1).prime.ne_zero)
  obtain ⟨a, ha⟩ := weak_approx (fun q => ((Gs u v hg).pl q).1) (pl_inj Gs u v hg)
    (fun q => (Gs u v hg).eQ q _ rfl (algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q) (y q)))
    (((D.what₂.places.resChar v : ℕ) : D.host.F) ^ N) (pow_ne_zero _ hp0)
  refine ⟨a, fun q => ?_⟩
  obtain ⟨z, hz⟩ := step _ ((Gs u v hg).eQ q _ rfl) ((Gs u v hg).completion_integers_iff q _ rfl) _ N hp0 a (y q) (ha q)
  exact ⟨z, (splitPlaceEmbedding_baseField_eq_completion Gs u v hg q a).trans hz⟩

theorem exists_global_lattice (n : ℕ)
    (L : ∀ q : Fin (D.gat u v hg).P.nV, Submodule ((D.gat u v hg).P.W q) (Fin n → (D.gat u v hg).P.Qq q)) :
    (∀ q, G.IsLattice ((D.gat u v hg).P.W q) (L q)) →
    ∃ Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E), ∀ q,
      L q = Submodule.span ((D.gat u v hg).P.W q) {y | ∃ x ∈ Λ, y = fun i => KerOne.iw0 Gs u v hg q (x i)} := by
  intro hL
  choose g hgu hgL using hL
  have hfr : ∀ q, IsFractionRing ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q) :=
    fun q => ((D.gat u v hg).P.setting q).frac_alt
  let Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
    { carrier := {x | ∀ q, (fun i => KerOne.iw0 Gs u v hg q (x i)) ∈ L q}
      add_mem' := fun {x y} hx hy q => by
        have : (fun i => KerOne.iw0 Gs u v hg q ((x + y) i)) =
            (fun i => KerOne.iw0 Gs u v hg q (x i)) + fun i => KerOne.iw0 Gs u v hg q (y i) := by
          funext i; simp
        rw [this]; exact (L q).add_mem (hx q) (hy q)
      zero_mem' := fun q => by
        have : (fun i => KerOne.iw0 Gs u v hg q ((0 : Fin n → D.host.E) i)) = 0 := by funext i; simp
        rw [this]; exact (L q).zero_mem
      smul_mem' := fun r x hx q => by
        obtain ⟨c, hc⟩ := splitPlaceEmbedding_integers_mem_localIntegers Gs u v hg q r
        have : (fun i => KerOne.iw0 Gs u v hg q ((r • x) i)) = c • fun i => KerOne.iw0 Gs u v hg q (x i) := by
          funext i
          rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, ← hc, Algebra.smul_def]
        rw [this]; exact (L q).smul_mem c (hx q) }
  refine ⟨Λ, fun q0 => ?_⟩
  obtain ⟨B, w, hw, hB, hoff⟩ := matrix_approx (fun q => (D.gat u v hg).P.W q) (fun q => (D.gat u v hg).P.Qq q)
    (fun q => (KerOne.iw0 Gs u v hg q).comp (algebraMap D.host.F D.host.E))
    (fun q => ((D.what₂.places.resChar v : ℕ) : (D.gat u v hg).P.W q)) (fun q => ((D.gat u v hg).P.setting q).p_unif)
    ((D.what₂.places.resChar v : ℕ) : D.host.F) (fun q => by rw [map_natCast, map_natCast])
    (fun y N => dense Gs u v hg y N) g hgu q0
  have hcol : ∀ c, (fun i => algebraMap D.host.F D.host.E (B i c)) ∈ Λ := by
    intro c q
    by_cases hq : q = q0
    · subst hq
      have : (fun i => KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E (B i c))) =
          fun i => (g q * w.map (algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q))) i c := by
        funext i; exact congrFun (congrFun hB i) c
      show (fun i => KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E (B i c))) ∈ L q
      rw [this, hgL q, ← colSpan_mul_eq (g q) w hw]
      exact Submodule.subset_span ⟨c, rfl⟩
    · show (fun i => KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E (B i c))) ∈ L q
      rw [hgL q]; exact hoff q hq c
  apply le_antisymm
  · rw [hgL q0, ← colSpan_mul_eq (g q0) w hw, Formalism.MainNotions.G.colSpan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    refine Submodule.subset_span ⟨_, hcol c, ?_⟩
    funext i; exact (congrFun (congrFun hB i) c).symm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx q0

end GlobalTheory.Mem.Top.KerGlob
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.OmExt.RootUpd

open Formalism.DivisionValues

variable {D : D7}

theorem exists_unit_of_pow (a : D.what₂.LL) (n : ℕ) (hn : n ≠ 0) (ha : a ^ n = 1) :
    ∃ u : (𝓞 D.what₂.LL)ˣ, ((u : 𝓞 D.what₂.LL) : D.what₂.LL) = a ∧ a ∈ Formalism.DivisionValues.cmMax D.what₂.LL ∧ star a * a = 1 := by
  have hσ : ∀ σ : D.what₂.LL →+* ℂ, ‖σ a‖ = 1 := fun σ => by
    have h : (σ a) ^ n = 1 := by rw [← map_pow, ha, map_one]
    exact Complex.norm_eq_one_of_pow_eq_one h hn
  have hconj : ∀ z : ℂ, ‖z‖ = 1 → starRingEnd ℂ z = z⁻¹ := fun z hz => by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
    simp
  have a0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at ha
    exact zero_ne_one ha
  have m0 : D.what₂.embLL a ≠ 0 := (map_ne_zero _).2 a0
  have h2 : star a * a = 1 := D.what₂.embLL.injective (by
    rw [map_mul, D.starLL_cx, hconj _ (hσ _), inv_mul_cancel₀ m0, map_one])
  have hs : star a = a⁻¹ := eq_inv_of_mul_eq_one_left h2
  have h1 : a ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
    change ∀ σ : D.what₂.LL →+* ℂ, σ (star a) = starRingEnd ℂ (σ a)
    intro σ
    rw [hs, map_inv₀, hconj _ (hσ σ)]
  have hi : IsIntegral (𝓞 D.what₂.LL) a := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [ha]
    exact isIntegral_one
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  have hx1 : x ^ n = 1 := IsFractionRing.injective (𝓞 D.what₂.LL) D.what₂.LL (by rw [map_pow, hx, ha, map_one])
  refine ⟨(IsUnit.of_pow_eq_one hx1 hn).unit, ?_, h1, h2⟩
  rw [IsUnit.unit_spec]
  exact hx

theorem coefMapTie_smul {V C lam c0 rho} (h : Formalism.IndefR.Bridge.CoefMapTie (D := D) V C (lam := lam) c0 rho) {μ : ℂ} (hμ : μ ≠ 0) :
    Formalism.IndefR.Bridge.CoefMapTie V C (μ • c0) rho := by
  obtain ⟨a1, a2, a3⟩ := h
  refine ⟨fun γ γE hγ v => by simp [a1 γ γE hγ v], a2.units_smul fun _ => Units.mk0 _ hμ, ?_⟩
  rw [eq_top_iff, ← a3, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have := Submodule.smul_mem _ μ⁻¹ (Submodule.subset_span (R := ℂ)
    (s := Set.range fun i => (μ • c0) (bVV D.what₂.LL lam i)) ⟨i, rfl⟩)
  exact Set.mem_of_eq_of_mem (inv_smul_smul₀ hμ (c0 _)).symm this

theorem coefTie_smul {V C S J χ P lam c0 pair nab del}
    (h : Formalism.IndefR.Bridge.CoefTie (D := D) V C (S := S) (J := J) (χ := χ) P lam c0 pair nab del)
    (l : D.what₂.LL) (u : (𝓞 D.what₂.LL)ˣ) (hu : ((u : 𝓞 D.what₂.LL) : D.what₂.LL) = l) (h1 : l ∈ Formalism.DivisionValues.cmMax D.what₂.LL)
    (h2 : star l * l = 1) :
    Formalism.IndefR.Bridge.CoefTie V C P lam (D.what₂.embLL l • c0) pair nab del := by
  have l0 : l ≠ 0 := right_ne_zero_of_mul_eq_one h2
  have m0 : D.what₂.embLL l ≠ 0 := (map_ne_zero _).2 l0
  have li : (((u⁻¹ : (𝓞 D.what₂.LL)ˣ) : 𝓞 D.what₂.LL) : D.what₂.LL) = l⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← hu, ← map_mul (algebraMap (𝓞 D.what₂.LL) D.what₂.LL), Units.inv_mul, map_one])
  obtain ⟨e, a1, a2, a3, a4, a5⟩ := h
  let s := LinearEquiv.smulOfNeZero D.what₂.LL (VV D.what₂.LL lam) l⁻¹ (inv_ne_zero l0)
  have hs : ∀ x, (e.trans s) x = l⁻¹ • e x := fun _ => rfl
  have hm : ∀ N : Submodule (𝓞 D.what₂.LL) S.V,
      N.map ((e.trans s).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) =
        N.map (e.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := fun N => by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨((u⁻¹ : (𝓞 D.what₂.LL)ˣ) : 𝓞 D.what₂.LL) • v, N.smul_mem _ hv, ?_⟩
      rw [← algebraMap_smul D.what₂.LL]
      exact (map_smul e _ _).trans (congrArg (· • e v) li)
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(u : 𝓞 D.what₂.LL) • v, N.smul_mem _ hv, ?_⟩
      rw [← algebraMap_smul D.what₂.LL]
      show (e.trans s) ((algebraMap (𝓞 D.what₂.LL) D.what₂.LL (u : 𝓞 D.what₂.LL)) • v) = e v
      rw [show algebraMap (𝓞 D.what₂.LL) D.what₂.LL (u : 𝓞 D.what₂.LL) = l from hu]
      exact (hs _).trans ((congrArg (l⁻¹ • ·) (map_smul e l v)).trans (inv_smul_smul₀ l0 _))
  refine ⟨e.trans s, fun i j => ?_, fun x => ?_, fun x x' => ?_, fun c => (hm _).trans (a4 c), fun c => (hm _).trans (a5 c)⟩
  · rw [hs, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem (inv_mem h1) (a1 i j)
  · rw [hs, LinearMap.smul_apply, map_smulₛₗ, map_inv₀, smul_inv_smul₀ m0, a2]
  · rw [hs, hs, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, a3, smul_smul, starRingEnd_apply, star_inv₀,
      ← mul_inv, mul_comm, h2, inv_one, one_smul]

end GlobalTheory.Mem.R3.Rw.OmExt.RootUpd

namespace GlobalTheory.Mem.R3.Rw.OmExt



theorem coefFam_update_root : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (c0L : ∀ i : Fin D.R.m, Formalism.IndefR.FWT.VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W),
    GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R c0L → ∀ (i : Fin D.R.m) (a : D.what₂.LL) (n : ℕ), n ≠ 0 → a ^ n = 1 →
    GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R (Function.update c0L i (D.what₂.embLL a • c0L i)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R c0L hc i a n hn ha
  obtain ⟨u, hu, h1, h2⟩ := RootUpd.exists_unit_of_pow a n hn ha
  have m0 : D.what₂.embLL a ≠ 0 := (map_ne_zero _).2 (right_ne_zero_of_mul_eq_one h2)
  obtain ⟨gramR, c0R, ht⟩ := hc
  refine ⟨gramR, c0R, ⟨ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, ht.ok, ht.gramR_eq, ht.mapR, fun j => ?_,
    ht.coefR, fun j t => ?_⟩⟩
  · rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]
      exact RootUpd.coefMapTie_smul (ht.mapL j) m0
    · rw [Function.update_of_ne hj]
      exact ht.mapL j
  · rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]
      exact RootUpd.coefTie_smul (ht.coefL j t) a u hu h1 h2
    · rw [Function.update_of_ne hj]
      exact ht.coefL j t

end GlobalTheory.Mem.R3.Rw.OmExt

end
end
