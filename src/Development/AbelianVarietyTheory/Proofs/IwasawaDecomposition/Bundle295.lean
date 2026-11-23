module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle194
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinTensAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1620
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
import Formalism.LocalToGlobal.GlobalTheory.GL6.PRLocV
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle008
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.LatSOfLocBasis
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelIndexLevelUnipotentCoprimePrime
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle285
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.FinDatum

theorem isRoots_sign {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {r n N : ℕ} {L : Lt E r} {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (ε : ℤˣ) (hN : l.M ∣ N)
    {Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E} (h : IsRoots l L ((ε : ℤ) • mk) N Y) :
    IsRoots l L mk l.M fun q => (ε : ℤ) • Y q := by
  intro q b
  obtain ⟨⟨a, ha, h1, h2⟩, j, hj⟩ := h q b
  obtain ⟨m, rfl⟩ := hN
  refine ⟨⟨a, ha, h1, ?_⟩, j, fun s hs => ?_⟩
  · have h3 := zsmul_mem h2 (ε : ℤ)
    rw [smul_sub, LinearMap.smul_apply, smul_comm (l.M : E)⁻¹, smul_smul, ← Units.val_mul, Int.units_mul_self,
      Units.val_one, one_smul] at h3
    exact h3
  · obtain ⟨u, hu, e⟩ := hj s hs
    refine ⟨(ε : ℤ) • m • u, zsmul_mem (nsmul_mem hu m) _, ?_⟩
    show s • (ε : ℤ) • Y q b = _
    rw [smul_comm s, e, smul_comm (2 * l.M), smul_smul (2 * l.M), mul_assoc]

variable {D : D7}

theorem lat_iotaW (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) :
    LatEmb (Wc D i) (iotaW T i) ∧ LatIsom (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).EF (iotaW T i) := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨hr, g, e, F, ik, φ, th, h, h', -⟩ := hT.adPin _ hj _ T.toCore.good_σ₀
  have hV := hT.spaceW _ hj _ T.toCore.good_σ₀
  have key : ∀ (V : HSp D) (hr : V.rank = D.R.r), V = Wc D i →
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatIsom V (T.Q.Dw ((i : ℕ) + 1)).EF
        (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatEmb (Wc D i) (iotaW T i) ∧ LatIsom (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).EF (iotaW T i) := by
    rintro V hr rfl h h'
    exact ⟨h, h'⟩
  exact key _ hr hV h h'

theorem latR_range {E : Type} [Field E] [NumberField E] {m r : ℕ} (hr : m = r) {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin r → E)) :
    GlobalTheory.AdTh.latR hr (LinearMap.range (LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι)) = LinearMap.range ι := by
  subst hr
  unfold GlobalTheory.AdTh.latR
  rw [← LinearMap.range_comp]
  rfl

theorem splitOffBad_one (V : HSp D) : SplitOffBad V 0 1 := by
  refine ⟨one_mem _, 0, ∅, ⟨⟨fun _ => 0, fun _ h => absurd h (Finset.notMem_empty _), by simp⟩, zero_mul _⟩,
    fun _ h => absurd h (Finset.notMem_empty _), fun i j => ?_⟩
  rw [show Formalism.L2.Theta.mt V 1 = 1 from rfl, sub_self, Matrix.zero_apply, mul_zero]

theorem isFinOf_finR (S T : HSp D) {r : ℕ} (hr : T.rank = r) (y : Matrix (Fin S.rank) (Fin r) D.host.E) :
    GlobalTheory.AdTh.colsR hr (y.submatrix id (Fin.cast hr))ᵀ = y ∧
      GlobalTheory.AdTh.IsFinOf S T (y.submatrix id (Fin.cast hr))ᵀ (finR S hr y) := by
  subst hr
  exact ⟨rfl, (GlobalTheory.VacSign.isFinOf_iff _ _).2 rfl⟩

theorem mem_std_star (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {n : ℕ} (v : Fin n → D.host.E)
    (h : v ∈ Formalism.L2.Pj.stdLat D.host.E n) : (fun j => star (v j)) ∈ Formalism.L2.Pj.stdLat D.host.E n := by
  intro j _
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h j trivial)
  exact Submodule.mem_one.2 ⟨H.bar a, (H.bar_eq a).trans (congrArg star ha)⟩

theorem smul_eq_zero_of_smul_rep {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (q : LevQ Dw l) (s : 𝓞 E) (z : Dw.La) (hz : s • (cSep l • levRep q) = l.M • z) :
    s • q = 0 := by
  have hrep : (Submodule.Quotient.mk (levRep q) : LevQ Dw l) = q :=
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  rw [← hrep, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hM : (l.M : 𝓞 E) ∈ l.Mb := Ideal.mul_le_left (l.prod.ge (Ideal.subset_span rfl))
  have e : s • levRep q = (l.M : 𝓞 E) • z - (cSep l - 1) • s • levRep q := by
    rw [Nat.cast_smul_eq_nsmul, ← hz, sub_smul, one_smul, smul_comm s, sub_sub_cancel]
  rw [e]
  exact sub_mem (Submodule.smul_mem_smul hM trivial) (Submodule.smul_mem_smul (LevelPairing.cSep_spec _).2 trivial)


end GlobalTheory.OneMapRef.FinDatum
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem mulVec_congr {A : Type} [CommRing A] {n N : ℕ} (P Q : Matrix (Fin n) (Fin n) A) {x y w : Fin n → A}
    (e : x - Q *ᵥ y = N • w) : P *ᵥ x - (P * Q) *ᵥ y = N • P *ᵥ w := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, e, Matrix.mulVec_smul]

theorem latW_rfl {D : D7} {W : HSp D} (L : Lt D.host.E W.rank) : latW (T := W) rfl L = L := rfl

section

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {W : HSp D}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)} {h : GA D W}

theorem markAd_rfl (l : Level H) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) :
    MarkAd (T := W) rfl l ι h mk ↔ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat W h,
      finVec W (mk a) - (finHom W h).1 *ᵥ (finVec W (ι a)) = l.M • w := Iff.rfl

theorem finVec_add' (a b : Fin W.rank → D.host.E) : finVec W (a + b) = finVec W a + finVec W b :=
  GlobalTheory.AdLat.cap_fv_add D.host.F a b

theorem finVec_nsmul' (n : ℕ) (a : Fin W.rank → D.host.E) : finVec W (n • a) = n • finVec W a :=
  GlobalTheory.AdLat.cap_fv_nsmul D.host.F n a

theorem finVec_sub' (a b : Fin W.rank → D.host.E) : finVec W (a - b) = finVec W a - finVec W b :=
  funext fun _ => TensorProduct.tmul_sub _ _ _

theorem markOver_of_markAd {l l₂ : Level H} (hM : l.M ∣ l₂.M) (hI : Mfr l₂ ≤ Mfr l)
    {mk mk₂ : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)} (h1 : MarkAd (T := W) rfl l ι h mk)
    (h2 : MarkAd (T := W) rfl l₂ ι h mk₂) : MarkOver l l₂ (latG W h) mk mk₂ := by
  intro a ha
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨c, hc⟩ := hM
  obtain ⟨w, hw, e⟩ := (markAd_rfl l mk).1 h1 a (Submodule.smul_mono_left hI ha)
  obtain ⟨w', hw', e'⟩ := (markAd_rfl l₂ mk₂).1 h2 a ha
  obtain ⟨u, hu, eu⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0 (mk₂ a - mk a) (c • w' - w)
    ((finVec_sub' _ _).trans (GlobalTheory.AdMark.sub_congr hc e e'))
  refine ⟨u, ((GlobalTheory.MarkCoset.latG_spec D W h).1 u).2 (hu ▸ sub_mem (nsmul_mem hw' c) hw), ?_⟩
  rw [← eu]
  abel

theorem finHom_mulVec_finVec {δ : GA D W} {ga : GL (Fin W.rank) D.host.E}
    (hδ : Formalism.L2.Theta.mt W δ = (ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D))
    (v : Fin W.rank → D.host.E) : (finHom W δ).1 *ᵥ finVec W v = finVec W (ga.1 *ᵥ v) := by
  funext i
  have hf : ∀ i j, (finHom W δ).1 i j = (1 : Af D.host.F) ⊗ₜ ga.1 i j := fun i j => by
    have he' : (matHom W δ).1 i j = (1 : AF D.host.F) ⊗ₜ ga.1 i j := congrFun (congrFun hδ i) j
    change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom W δ).1 i j) = _
    rw [he', Algebra.TensorProduct.map_tmul, map_one]
    rfl
  simp only [Matrix.mulVec, dotProduct, hf, finVec, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
    TensorProduct.tmul_sum]

theorem mem_latGHat_mul (δ : GA D W) (z : Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom W δ).1 *ᵥ z ∈ latGHat W (δ * h) ↔ z ∈ latGHat W h := by
  rw [(GlobalTheory.MarkCoset.latG_spec D W h).2, (GlobalTheory.MarkCoset.latG_spec D W (δ * h)).2]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  refine ⟨fun e => ?_, fun e => by rw [e]⟩
  have := congrArg (fun v => ((finHom W δ)⁻¹).1 *ᵥ v) e
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Units.inv_mul_cancel_left] at this
  exact this

end

theorem markAd_laws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (W : HSp D) (r : ℕ) (hr : W.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → ∀ (h : GA D W) (L : Lt D.host.E r), latW hr L = latG W h → ∀ l : Level H, (∃ mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk a ∈ L) ∧ MarkAd hr l ι h mk) ∧ ∀ mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk a ∈ L) → MarkAd hr l ι h mk → IsMark l L mk ∧ (∀ mk' : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ u ∈ L, mk' a = mk a + l.M • u) → MarkAd hr l ι h mk') ∧ (∀ l₂ : Level H, l.M ∣ l₂.M → Mfr l₂ ≤ Mfr l → ∀ mk₂ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk₂ a ∈ L) → MarkAd hr l₂ ι h mk₂ → MarkOver l l₂ L mk mk₂) ∧ ∀ (δ : GA D W) (ga : GL (Fin r) D.host.E), Formalism.L2.Theta.mt W δ = ((ga : Matrix (Fin r) (Fin r) D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)).map (incA D) → latW hr (mapL ga L) = latG W (δ * h) ∧ MarkAd hr l ι (δ * h) (mvMap ga mk) := by
  intro D H Dw W r hr ι hι h L hL l
  subst hr
  rw [latW_rfl] at hL
  subst hL
  obtain ⟨mk₀, hm0, ha0, -⟩ := GlobalTheory.AdMark.exists_marking D H Dw l l W _ rfl ι hι dvd_rfl le_rfl h
  rw [GlobalTheory.AdMark.latR_rfl] at hm0
  replace ha0 : MarkAd (T := W) rfl l ι h mk₀ := ha0
  refine ⟨⟨mk₀, hm0.mem, ha0⟩, fun mk hmem hmk => ⟨?_, ?_, ?_, ?_⟩⟩
  · have ho := markOver_of_markAd dvd_rfl le_rfl hmk ha0
    refine ⟨hmem, ?_, fun v hv => ?_⟩
    · rintro a ha ⟨u, hu, e⟩
      obtain ⟨u', hu', e'⟩ := ho a ha
      exact hm0.inj a ha ⟨u + u', add_mem hu hu', by rw [e', e, smul_add]⟩
    · obtain ⟨a, ha, u, hu, e⟩ := hm0.surj v hv
      obtain ⟨u', hu', e'⟩ := ho a ha
      exact ⟨a, ha, u' + u, add_mem hu' hu, by rw [e, e', smul_add, add_assoc]⟩
  · intro mk' hc
    refine (markAd_rfl l mk').2 fun a ha => ?_
    obtain ⟨u, hu, e⟩ := hc a ha
    obtain ⟨w, hw, e'⟩ := (markAd_rfl l mk).1 hmk a ha
    refine ⟨w + finVec W u, add_mem hw (((GlobalTheory.MarkCoset.latG_spec D W h).1 u).1 hu), ?_⟩
    rw [e, finVec_add', finVec_nsmul', smul_add, ← e']
    abel
  · intro l₂ hM hI mk₂ _ h2
    exact markOver_of_markAd hM hI hmk h2
  · intro δ ga hδ
    have hf := finHom_mulVec_finVec (δ := δ) (ga := ga) hδ
    constructor
    · rw [latW_rfl]
      ext v
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ((GlobalTheory.MarkCoset.latG_spec D W (δ * h)).1 _).2 ?_
        change finVec W (ga.1 *ᵥ x) ∈ _
        rw [← hf, mem_latGHat_mul]
        exact ((GlobalTheory.MarkCoset.latG_spec D W h).1 _).1 hx
      · intro hv
        have hri : ga.1 *ᵥ ((ga⁻¹).1 *ᵥ v) = v := by
          rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
        refine ⟨(ga⁻¹).1 *ᵥ v, ((GlobalTheory.MarkCoset.latG_spec D W h).1 _).2 ?_, hri⟩
        rw [← mem_latGHat_mul δ, hf, hri]
        exact ((GlobalTheory.MarkCoset.latG_spec D W (δ * h)).1 _).1 hv
    · refine (markAd_rfl l _).2 fun a ha => ?_
      obtain ⟨w, hw, e⟩ := (markAd_rfl l mk).1 hmk a ha
      refine ⟨_, (mem_latGHat_mul δ w).2 hw, ?_⟩
      change finVec W (ga.1 *ᵥ mk a) - _ = _
      rw [← hf, map_mul, Units.val_mul]
      exact mulVec_congr _ _ e

end GlobalTheory.OneMapRef
end

section

noncomputable section

namespace GlobalTheory.LevelHecke

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]




theorem nsmul_latS_of_nsmul {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (L M : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ z ∈ M, T • z ∈ L) (w : Fin n → E ⊗[F] v.adicCompletion F)
    (hw : w ∈ latS (F := F) (v.adicCompletion F) (intV E v) M) :
    T • w ∈ latS (F := F) (v.adicCompletion F) (intV E v) L := by
  have key : ∀ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) M,
      T • x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L := by
    intro x hx
    unfold latS at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨T • z, h z hz, ?_⟩
      funext i
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  exact key w hw




theorem nsmul_dual_mem_loc {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (hJ : IsUnit J.det)
    (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hy : y ∈ UPts σ J (v.adicCompletion F))
    (hyl : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔
      (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb)
    (z : Fin n → E) (hz : z ∈ dualL (σ : E →+* E) J L) :
    ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • T • z ∈ L := by
  have hLb : Submodule.IsFullLattice E S.Lb :=
    { toIsLattice := Submodule.IsLattice.of_fg E (Module.Finite.iff_fg.mp S.Lb_fin)
      span_eq_top := S.Lb_span }

  have hT : ∀ x ∈ dualL (σ : E →+* E) J S.Lb, T • x ∈ S.Lb := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => rw [← Nat.cast_smul_eq_nsmul E]; exact S.Lb_dual x hx
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  let zV : Fin n → E ⊗[F] v.adicCompletion F := fun a => inclE (F := F) (v.adicCompletion F) (z a)
  have hdual : (y⁻¹).1 *ᵥ zV ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J S.Lb) := by
    apply (GlobalTheory.DualCompletion.mem_latS_dualL σ J hJ v S.Lb hLb _).2
    intro u hu
    have huL : y.1 *ᵥ u ∈ latS (F := F) (v.adicCompletion F) (intV E v) L := by
      apply (hyl _).2
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hyU : cT (sigR σ (v.adicCompletion F)) y.1 *
        J.map (inclE (F := F) (v.adicCompletion F)) * y.1 =
        J.map (inclE (F := F) (v.adicCompletion F)) := hy
    have hpair := Formalism.UG.P.hform_mulVec (sigR σ (v.adicCompletion F))
      (J.map (inclE (F := F) (v.adicCompletion F))) y.1 u ((y⁻¹).1 *ᵥ zV)
    rw [hyU, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at hpair
    rw [← hpair]
    exact Formalism.L2.G.RelativeIndexFlags.pair_int v σ J L z
      ((GlobalTheory.DualCompletion.mem_dualL (σ : E →+* E) J L z).1 hz) _ huL
  have h2 := nsmul_latS_of_nsmul v T S.Lb (dualL (σ : E →+* E) J S.Lb) hT _ hdual
  rw [← Matrix.mulVec_smul] at h2
  have h3 := (hyl _).mpr h2
  have h4 : (fun a => inclE (F := F) (v.adicCompletion F) ((T • z) a)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) L := by
    convert h3 using 1
    funext a
    simp only [zV, Pi.smul_apply, map_nsmul]
  exact GlobalTheory.T.exists_smul_mem_lattice_of_mem_completion F E v n L hL (T • z) h4




theorem nsmul_dual_mem_loc_adelic {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (hJ : IsUnit J.det)
    (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hyl : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔
      (y.1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb)
    (z : Fin n → E) (hz : z ∈ dualL (σ : E →+* E) J L) :
    ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • T • z ∈ L := by
  have hloc : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔
      ((bc (prV (E := E) v) y.1)⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
    intro x
    rw [← map_inv]
    exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.rlv_yloc v y.1 hyl x
  exact nsmul_dual_mem_loc S hJ v L hL _ (Formalism.UG.P.afsplit_bc_mem σ J v y.1 y.2) hloc z hz

end Core

theorem loc_sup_ker_smul {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k] (res : R →+* k) (t : R)
    (hu : Unram res t) (M N : Submodule R V) (h : ∀ z ∈ N, t • z ∈ loc res M) :
    loc res (M ⊔ RingHom.ker res • N) = loc res M := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_loc res _ x).mp hx
    have hle : M ⊔ RingHom.ker res • N ≤ loc res M := by
      refine sup_le (le_loc res M) ?_
      rw [Submodule.smul_le]
      intro a ha z hz
      obtain ⟨s', b, hs', hsab⟩ := hu.2 a (RingHom.mem_ker.mp ha)
      apply loc_sat res M s' _ hs'
      rw [smul_smul, hsab, mul_comm, ← smul_smul]
      exact Submodule.smul_mem _ b (h z hz)
    exact loc_sat res M s x hs (hle hsx)
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_loc res M x).mp hx
    exact (mem_loc res _ x).mpr ⟨s, hs, Submodule.mem_sup_left hsx⟩




theorem loc_lk_eq_loc_cls : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i), loc (A.res v) (Lk A i hi v c) = loc (A.res v) (clsCrd D u i hi c) := by
  intro D u A i hi K v c
  refine loc_sup_ker_smul (A.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) (GlobalTheory.T.levelPrime_unramifiedUniformizer D u A v) _ _ ?_
  intro z hz
  obtain ⟨r, hr, hrz⟩ := nsmul_dual_mem_loc_adelic K.lev (bwB_gramN_det D i hi) (A.eV v).1
    (clsCrd D u i hi c) (bwB_clsCrd_lat D u i hi c) (K.y c) (K.y_lat c) z hz
  refine (mem_loc _ _ _).mpr ⟨algebraMap _ _ r, fun h0 => hr ((A.res_v v r).mpr h0), ?_⟩
  rwa [Nat.cast_smul_eq_nsmul]

end GlobalTheory.LevelHecke

end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem UA_ext_cEmb {a b : UA E n}
    (hfin : GeneralLinearGroup.map (pFin E) a.1 = GeneralLinearGroup.map (pFin E) b.1)
    (hinf : ∀ τ : E →+* ℂ, cEmb τ a = cEmb τ b) : a = b := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply Prod.ext
  · have key : pInf E (a.1.1 i j) = pInf E (b.1.1 i j) := by
      funext w
      have h := congrArg (fun g : GL (Fin n) ℂ => g.1 i j) (hinf w.embedding)
      simp only [cEmb, cInf, MonoidHom.comp_apply, GeneralLinearGroup.map, Subgroup.coe_subtype] at h
      change coord w.embedding (pInf E (a.1.1 i j)) = coord w.embedding (pInf E (b.1.1 i j)) at h
      have hw : InfinitePlace.mk w.embedding = w := InfinitePlace.mk_embedding w
      unfold coord at h
      rw [if_pos (by rw [hw])] at h
      simpa [hw] using h
    exact (infEq E).symm.injective key
  · have h := congrArg (fun g : GL (Fin n) (Af E) => g.1 i j) hfin
    exact h

theorem embU_commute (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ τ' : E →+* ℂ)
    (hne : InfinitePlace.mk τ ≠ InfinitePlace.mk τ') : ∀ x ∈ embU n τ, ∀ y ∈ embU n τ', Commute x y := by
  intro x hx y hy
  simp only [embU, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker] at hx hy
  obtain ⟨hxf, hxi⟩ := hx
  obtain ⟨hyf, hyi⟩ := hy
  rw [infU, MonoidHom.mem_ker] at hxf hyf
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hxf hyf
  apply UA_ext_cEmb
  · simp only [Subgroup.coe_mul, map_mul, hxf, hyf]
  · intro σ
    simp only [map_mul]
    by_cases h : InfinitePlace.mk σ = InfinitePlace.mk τ
    · have : InfinitePlace.mk σ ≠ InfinitePlace.mk τ' := h ▸ hne
      rw [hyi σ this, one_mul, mul_one]
    · rw [hxi σ h, one_mul, mul_one]

end GlobalTheory.UnitaryBC
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.L2
open Formalism.AUTREP (GAf)

theorem _root_.GlobalTheory.T.relIndex_levelUnipotent_coprime_prime : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (r p : ℕ) (H : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))), p.Prime → s.Above p → r ≤ n → (∀ g, g ∈ H ↔ NG.UniRT s r g) → Nat.Coprime (H.relIndex (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring)) p := by
  first | exact @GlobalTheory.UniLevelIndex.relIndex_coprime | exact GlobalTheory.UniLevelIndex.relIndex_coprime | (intros; apply GlobalTheory.UniLevelIndex.relIndex_coprime <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_cyclotomic_unramified_completed_integers : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ), ∃ _ : IsDiscreteValuationRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), IsAlgClosed (IsLocalRing.ResidueField ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧ IsAdic (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ (∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∀ y ∈ clC l (Kt l K₀ L ⊔ muK l k), ‖x‖ ≤ ‖y‖ → x / y ∈ clC l (Kt l K₀ L ⊔ muK l k)) ∧ muK l 0 = ⊥ ∧ (∃ T : Finset ℂ_[l], ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ Submodule.span ↥(clC l (Kt l K₀ L)) (T : Set ℂ_[l])) ∧ ∃ ζ ∈ clC l (Kt l K₀ L ⊔ muK l k), IsPrimitiveRoot ζ (l ^ k) ∧ ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ (p : Polynomial ↥(clC l (Kt l K₀ L))) (d : ↥(clC l (Kt l K₀ L))), d ≠ 0 ∧ x * (d : ℂ_[l]) = Polynomial.aeval ζ p := by
  first | exact @GlobalTheory.CycClosure.exists_cyclotomic_integers | exact GlobalTheory.CycClosure.exists_cyclotomic_integers | (intros; apply GlobalTheory.CycClosure.exists_cyclotomic_integers <;> assumption)
end
