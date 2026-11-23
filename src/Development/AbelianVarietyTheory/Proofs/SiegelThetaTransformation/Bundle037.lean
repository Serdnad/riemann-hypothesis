module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MultAddMultConjugate
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NeBotOfNorm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle033
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

noncomputable section

namespace GlobalTheory.BetaChange

open GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.LatticeBetaCompare GlobalTheory.SW.Nbr
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem form_adj (h : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    ∑ j, IsCMField.complexConj E (v j) * h.mulVec w j =
      ∑ j, IsCMField.complexConj E ((adjM h).mulVec v j) * w j := by

  simp only [Matrix.mulVec, dotProduct, adjM, Matrix.of_apply, map_sum, map_mul,
  IsCMField.complexConj_apply_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem unimod_act {h : Matrix (Fin n) (Fin n) E} (hu : IsUnitaryM h) {Λ : GenLat E n} (hΛ : Λ.Unimod) :
    (actLat h Λ).Unimod := by
  have h1 : adjM h * h = 1 := hu
  have h2 : h * adjM h = 1 := mul_eq_one_comm.1 h1
  intro v
  have e : v ∈ (actLat h Λ).La ↔ (adjM h).mulVec v ∈ Λ.La := by
    constructor
    · rintro ⟨u, hu, rfl⟩
      change (adjM h).mulVec (h.mulVec u) ∈ _
      rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    · intro hv
      refine ⟨_, hv, ?_⟩
      change h.mulVec _ = _
      rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [e, hΛ]
  constructor
  · rintro hv _ ⟨u, hu, rfl⟩
    exact (form_adj h v u).symm ▸ hv u hu
  · intro hv w hw
    rw [← form_adj]
    exact hv _ ⟨w, hw, rfl⟩

variable {H : Host E} (Dw : Datum H) {l : Geo.Tor.Level H} (c : Coeff l)

theorem reflexNorm_mul_conj (g : 𝓞 E) :
    reflexNorm Dw c ((g * co g : 𝓞 E) : E) = ((Ideal.absNorm (Ideal.span {g}) ^ (Dw.p + Dw.q) : ℕ) : c.F) := by
  have h := (isBe_principal Dw c g).2 c.F.val.toRingHom
  apply c.F.val.toRingHom.injective
  rw [map_natCast]
  have e : c.F.val.toRingHom (reflexNorm Dw c ((g * co g : 𝓞 E) : E)) =
      c.F.val.toRingHom (reflexNorm Dw c (g : E)) * conj (c.F.val.toRingHom (reflexNorm Dw c (g : E))) := by
    simp only [reflexNorm, map_prod, map_pow, ← Finset.prod_mul_distrib, ← mul_pow]
    refine Finset.prod_congr rfl fun σ _ => ?_
    congr 1
    change σ ((g : E) * IsCMField.complexConj E (g : E)) = σ g * conj (σ g)
    rw [map_mul, IsCMField.complexEmbedding_complexConj]
  rw [e, Complex.mul_conj', ← Complex.ofReal_pow, h]
  push_cast
  rfl

theorem isBe_mul_conj (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) :
    IsBe Dw c (J * conjI J) ((Ideal.absNorm J ^ (Dw.p + Dw.q) : ℕ) : c.F) := by
  let I₀ : (Ideal (𝓞 E))⁰ := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩
  obtain ⟨k, hk, e⟩ := (isOfFinOrder_of_finite (ClassGroup.mk0 I₀)).exists_pow_eq_one
  rw [← map_pow] at e
  obtain ⟨g, hg⟩ : (J ^ k).IsPrincipal := (ClassGroup.mk0_eq_one_iff (I₀ ^ k).2).1 e
  change J ^ k = Ideal.span {g} at hg
  refine isBe_of_pow hk ?_
  have e1 : (J * conjI J) ^ k = Ideal.span {g * co g} := by
    rw [mul_pow, conjI_eq, ← Ideal.map_pow, hg, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_mul_span_singleton]
  have e2 : ((Ideal.absNorm J ^ (Dw.p + Dw.q) : ℕ) : c.F) ^ k = reflexNorm Dw c ((g * co g : 𝓞 E) : E) := by
    rw [reflexNorm_mul_conj, ← hg, map_pow, ← Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm k]
  rw [e1, e2]
  exact isBe_principal Dw c _

theorem isBe_of_isBeta {Λ : GenLat E n} (hΛ : Λ.Unimod) {b : c.F} (hb : IsBeta Dw c Λ b) {J : Ideal (𝓞 E)}
    (hN : Ideal.absNorm J = (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index)
    (hJ : detSpan Λ.Ln = J • detSpan Λ.La) : IsBe Dw c J b := by
  have hu0 : IsUnit (detSpan Λ.La) :=
    isUnit_detSpan (GenusLatCompare.latEquiv.symm ⟨Λ, GenusLatCompare.isLat_of_unimod Λ hΛ⟩)
  have hu : IsUnit (∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ) :=
    IsUnit.prod_iff.2 fun τ _ => by rw [idealAt_eq]; exact (hu0.map _).pow _
  obtain ⟨-, h1, h2⟩ := hb
  refine ⟨?_, fun s => by rw [hN]; exact h2 s⟩
  have e : ∀ τ, idealAt c Λ.Ln τ =
      coeI c.F (J.map (RingOfIntegers.mapRingHom (embF c τ))) * idealAt c Λ.La τ := fun τ => by
    rw [idealAt_eq, idealAt_eq, hJ, smul_eq_coeI_mul, map_mul, extend_coeI]
  rw [← span_eq_coeI_iff, coeI_reflexIdeal]
  rw [BetaIs] at h1
  simp only [e, mul_pow, Finset.prod_mul_distrib] at h1
  exact hu.mul_left_inj.1 h1

omit [IsCMField E] in
theorem map_mulLeft_eq (x : E) (M : Submodule (𝓞 E) E) :
    Submodule.map (LinearMap.mulLeft (𝓞 E) x) M = Submodule.span (𝓞 E) {x} * M := by
  ext y
  rw [Submodule.mem_span_singleton_mul]
  rfl

omit [IsCMField E] in
theorem coeI_span (u : 𝓞 E) : coeI E (Ideal.span {u}) = Submodule.span (𝓞 E) {(u : E)} :=
  IsLocalization.coeSubmodule_span_singleton E u

theorem beta_sq_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (n : ℕ) (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (b b' : c.F), Λ.Unimod → IsUnitaryM h → IsBeta Dw c Λ b → IsBeta Dw c (actLat h Λ) b' → ∃ m : ℕ, 0 < m ∧ (b ^ 2 * ((((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : c.F)) ^ m = (b' ^ 2 * ((((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : c.F) * ∏ τ : E →+* ℂ, embF c τ h.det ^ Dw.mult τ) ^ m := by
  intro E _ _ _ H Dw l c n Λ h b b' hΛ hu hb hb'
  have hΛ' := unimod_act hu hΛ
  obtain ⟨J, hJ0, hN, hJ1, hJ2, hdet⟩ := GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard E n Λ hΛ
  obtain ⟨J', hJ0', hN', hJ1', hJ2', -⟩ := GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard E n _ hΛ'
  have hB := isBe_of_isBeta Dw c hΛ hb hN hJ1
  have hB' := isBe_of_isBeta Dw c hΛ' hb' hN' hJ1'
  obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := 𝓞 E) h.det
  have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
  have hvE : (v : E) ≠ 0 := by simpa using hv0
  have huv' : (u : E) = h.det * (v : E) := by
    rw [← huv]; exact (div_mul_cancel₀ _ hvE).symm
  have k1 : coeI E (conjI J) = coeI E J * detSpan Λ.La := by
    rw [← smul_eq_coeI_mul]; exact hJ2.symm.trans hJ1
  have k2 : coeI E (conjI J') = coeI E J' * (Submodule.span (𝓞 E) {h.det} * detSpan Λ.La) := by
    rw [← smul_eq_coeI_mul, ← map_mulLeft_eq]
    exact (hJ2'.symm.trans hJ1').trans (by rw [hdet]; rfl)
  have key : conjI J' * J * Ideal.span {v} = conjI J * J' * Ideal.span {u} := by
    apply IsFractionRing.coeSubmodule_injective (𝓞 E) E
    change coeI E _ = coeI E _
    simp only [map_mul, k1, k2, coeI_span]
    rw [huv', ← Set.singleton_mul_singleton, ← Submodule.span_mul_span]
    ring
  have a1 := isBe_mul (isBe_mul (isBe_pow hB 2) (isBe_mul_conj Dw c J' hJ0')) (isBe_principal Dw c v)
  have a2 := isBe_mul (isBe_mul (isBe_pow hB' 2) (isBe_mul_conj Dw c J hJ0)) (isBe_principal Dw c u)
  have e : J' ^ 2 * (J * conjI J) * Ideal.span {u} = J ^ 2 * (J' * conjI J') * Ideal.span {v} := by
    calc _ = J * J' * (conjI J * J' * Ideal.span {u}) := by ring
      _ = _ := by rw [← key]; ring
  rw [e] at a2
  have hc : conjI J' ≠ ⊥ := fun h0 => hJ0' (by
    rw [← conjI_conjI J', h0, conjI_eq, Ideal.map_bot])
  have hs : Ideal.span {v} ≠ (⊥ : Ideal (𝓞 E)) := by simpa using hv0
  obtain ⟨z, hz, ez⟩ := isBe_unique
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hJ0) (mul_ne_zero hJ0' hc)) hs) a2 a1
  obtain ⟨m, hm, hzm⟩ := hz.exists_pow_eq_one
  have hψ : reflexNorm Dw c (v : E) ≠ 0 := isBe_ne_zero hs (isBe_principal Dw c v)
  have hψu : reflexNorm Dw c (u : E) = (∏ τ : E →+* ℂ, embF c τ h.det ^ Dw.mult τ) * reflexNorm Dw c (v : E) := by
    simp only [huv', reflexNorm, map_mul, mul_pow, Finset.prod_mul_distrib]
  rw [hψu, ← _root_.mul_assoc, ← _root_.mul_assoc, hN, hN'] at ez
  have ez' := mul_right_cancel₀ hψ ez
  refine ⟨m, hm, ?_⟩
  rw [ez', _root_.mul_assoc z, mul_pow z, hzm, _root_.one_mul]

end GlobalTheory.BetaChange
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StabProper

private lemma sum_mul_conj_eq_conj_dotProduct {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    ∑ a, ∑ b, x a * conj (G b a) * conj (y b) = conj (y ⬝ᵥ (G *ᵥ star x)) := by

  simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_conj]
  ring

theorem unitary_iff_form {n : ℕ} (G g : Matrix (Fin n) (Fin n) ℂ) :
    gᴴ * G * g = G ↔ ∀ v w : Fin n → ℂ,
      ∑ a, ∑ b, (g.map conj *ᵥ v) a * conj (G b a) * conj ((g.map conj *ᵥ w) b) =
        ∑ a, ∑ b, v a * conj (G b a) * conj (w b) := by
  have h1 : ∀ v : Fin n → ℂ, star (g.map conj *ᵥ v) = g *ᵥ star v := by
    intro v; ext i
    simp [mulVec, dotProduct]
  have key : ∀ v w : Fin n → ℂ, ∑ a, ∑ b, (g.map conj *ᵥ v) a * conj (G b a) * conj ((g.map conj *ᵥ w) b) =
      conj (w ⬝ᵥ ((gᴴ * G * g) *ᵥ star v)) := by
    intro v w
    rw [sum_mul_conj_eq_conj_dotProduct, h1]
    congr 1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w gᴴ]
    congr 1
    ext j
    simp [vecMul, mulVec, dotProduct, conjTranspose_apply, mul_comm]
  constructor
  · intro h v w
    rw [key, h, sum_mul_conj_eq_conj_dotProduct]
  · intro h
    ext i j
    have hs : ∀ k : Fin n, star (Pi.single k 1 : Fin n → ℂ) = Pi.single k 1 := by
      intro k; ext l; by_cases hl : l = k <;> simp [hl]
    have := h (Pi.single j 1) (Pi.single i 1)
    rw [key, sum_mul_conj_eq_conj_dotProduct, hs] at this
    have := (starRingEnd ℂ).injective this
    simpa [mulVec, dotProduct, Pi.single_apply] using this

variable {D : D7}

theorem compAt_eq (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (w : Mx D m n) :
    compAt θ τ w = w.map ((θ τ).comp (infPart D)) := rfl

theorem hermC_eq {S T : HSp D} (C : Ctx S T) (σ : C.X.Ψ) (v w : Fin T.rank → ℂ) :
    hermC σ.1 C.X.Gm v w = ∑ a, ∑ b, v a * conj (gramAt D T (C.m.e.symm σ) b a) * conj (w b) := by
  unfold hermC gramAt
  have he := C.m.e_emb (C.m.e.symm σ)
  rw [Equiv.apply_symm_apply] at he
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [C.m.gT, he]
  simp [NumberField.ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.StabProper

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.LatTens

noncomputable def gen {D : D7} (S T : HSp D) (α : Af D.host.F) :
    Matrix (Fin S.rank) (Fin T.rank) D.host.E →+ WO S T :=
  AddMonoidHom.mk' (fun y => Matrix.of fun a k => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a)
    fun y y' => Matrix.ext fun a k => TensorProduct.tmul_add _ (y k a) (y' k a)

def vmv {E : Type} [Field E] {n r : ℕ} (v : Fin n → E) : (Fin r → E) →+ Matrix (Fin n) (Fin r) E :=
  AddMonoidHom.mk' (fun u => vecMulVec v u)
    fun u u' => Matrix.ext fun k a => mul_add (v k) (u a) (u' a)

theorem gen_eq {D : D7} (S T : HSp D) (hS : S.gram = 1) (α : Af D.host.F) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T)
      = gen S T α (vecMulVec (star s) (a • t)) := by
  refine Matrix.ext fun i j => ?_
  simp only [gen, AddMonoidHom.mk'_apply, Matrix.of_apply]
  congr 1
  rw [hS]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, vecMulVec_apply, Pi.star_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem latO_eq_hatA : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (LS Λ : Lt D.host.E S.rank) (LT L : Lt D.host.E T.rank), (∀ v, v ∈ Λ ↔ star v ∈ LS) → IsAA L LT → latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) = hatA S T (tens Λ L) := by
  intro D S T C LS Λ LT L hΛ hL
  have hS : S.gram = 1 := C.m.gS

  have hmem : ∀ α : Af D.host.F, α ∈ intAf D.host.F → ∀ a : D.host.E, a ∈ D.host.AA →
      ∀ v : Fin S.rank → D.host.E, v ∈ Λ → ∀ t : Fin T.rank → D.host.E, t ∈ LT →
      gen S T α (vecMulVec v (a • t)) ∈ latO S T (LS : Set (Fin S.rank → D.host.E))
        (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro α hα a ha v hv t ht
    unfold latO
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, fun _ h => absurd trivial h, a, ha, star v, (hΛ v).1 hv, t, ht, ?_⟩
    rw [gen_eq S T hS α a (star v) t, star_star]
  apply le_antisymm
  · unfold latO
    rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    rw [gen_eq S T hS α a s t]
    unfold hatA
    apply AddSubgroup.subset_closure
    have hsΛ : star s ∈ Λ := (hΛ (star s)).2 (by rw [star_star]; exact hs)
    have htL : a • t ∈ L := (hL (a • t)).2 (AddSubgroup.subset_closure ⟨a, ha, t, ht, rfl⟩)
    exact ⟨α, hα, vecMulVec (star s) (a • t),
      AddSubgroup.subset_closure ⟨star s, hsΛ, a • t, htL, rfl⟩, rfl⟩
  · unfold hatA
    rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, y, hy, rfl⟩

    have hT : tens Λ L ≤ (latO S T (LS : Set (Fin S.rank → D.host.E))
        (LT : Set (Fin T.rank → D.host.E)) (fun _ => True)).comap (gen S T α) := by
      unfold tens
      rw [AddSubgroup.closure_le]
      rintro _ ⟨v, hv, u, hu, rfl⟩
      have hL' : AddSubgroup.closure {u | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ t ∈ LT, u = a • t} ≤
          (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
            (fun _ => True)).comap ((gen S T α).comp (vmv v)) := by
        rw [AddSubgroup.closure_le]
        rintro _ ⟨a, ha, t, ht, rfl⟩
        exact hmem α hα a ha v hv t ht
      exact hL' ((hL u).1 hu)
    exact hT hy

end GlobalTheory.Ker.LatTens
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.LevEig

section Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} {X : Data E r} (L : SW.Level X)


end Alg

section Hat

variable {D : D7} {k : ℕ}

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem tmul_mem_hatV {L : Lt D.host.E k} {a : Af D.host.F} (ha : a ∈ intAf D.host.F) {x : Fin k → D.host.E}
    (hx : x ∈ L) : (fun i => a ⊗ₜ[D.host.F] x i) ∈ hatV L :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem toAf_mem {L : Lt D.host.E k} {x : Fin k → D.host.E} (hx : x ∈ L) : toAf x ∈ hatV L :=
  tmul_mem_hatV one_mem_intAf hx

theorem toAf_sub (x y : Fin k → D.host.E) : toAf (x - y) = toAf x - toAf y := by
  funext i; exact TensorProduct.tmul_sub _ _ _

theorem hatV_map {G : Type} [AddCommGroup G] {L : Lt D.host.E k} (f : (Fin k → AfE D) →+ G) (H : AddSubgroup G)
    (h : ∀ a ∈ intAf D.host.F, ∀ x ∈ L, f (fun i => a ⊗ₜ[D.host.F] x i) ∈ H) {u} (hu : u ∈ hatV L) : f u ∈ H := by
  refine (AddSubgroup.closure_le (H.comap f)).2 ?_ hu
  rintro _ ⟨a, ha, x, hx, rfl⟩
  exact h a ha x hx

theorem smul_mem_hatV {L L' : Lt D.host.E k} (c : 𝓞 D.host.E) (h : ∀ x ∈ L, c • x ∈ L') {u} (hu : u ∈ hatV L) :
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • u ∈ hatV L' := by
  refine hatV_map (DistribSMul.toAddMonoidHom _ ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E))) _
    (fun a ha x hx => ?_) hu
  convert tmul_mem_hatV ha (h x hx) using 1
  ext i
  simp [smul_eq_mul, Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]

theorem nsmul_mem_hatV {L : Lt D.host.E k} {𝔪 : Ideal (𝓞 D.host.E)} {M : ℕ} (hM : (M : 𝓞 D.host.E) ∈ 𝔪) {u}
    (hu : u ∈ hatV L) : M • u ∈ hatV (𝔪 • L) := by
  have := smul_mem_hatV (L' := 𝔪 • L) M (fun x hx => Submodule.smul_mem_smul hM hx) hu
  have e : ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((M : 𝓞 D.host.E) : D.host.E)) = (M : AfE D) :=
    map_natCast ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F)).toRingHom.comp
      (algebraMap (𝓞 D.host.E) D.host.E)) M
  rwa [e, Nat.cast_smul_eq_nsmul] at this

theorem fmt_one (V : HSp D) : fmt V 1 = 1 := by
  simp only [fmt, Formalism.L2.Theta.mt, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

variable {S T : HSp D}

theorem actO_sub (h : GA D S) (g : GA D T) (w w' : WO S T) :
    actO S T h g (w - w') = actO S T h g w - actO S T h g w' := by
  simp only [actO, Matrix.mul_sub, Matrix.sub_mul]

end Hat

section Mov

variable {D : D7} {S T : HSp D}

end Mov

section Main

variable {D : D7} {S T : HSp D} (C : Ctx S T) (Lv : SW.Level C.X)

end Main

end GlobalTheory.Ker.LevEig
end
