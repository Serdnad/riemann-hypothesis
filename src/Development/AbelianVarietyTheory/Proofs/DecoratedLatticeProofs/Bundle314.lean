module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle288
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameValuesPolynomialDetStableHomogeneous
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle216
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle282
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle308
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharAnnihilatorOpenSubgroupFinPartCompact
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

open scoped ComplexOrder

namespace GlobalTheory.CenterVac

variable {D : D7}

theorem lintegral_enorm_sq_eq_one {α : Type} [MeasurableSpace α] {μ : Measure α} {s : Set α} {f : α → ℂ}
    (h : ∫ w in s, ‖f w‖ ^ 2 ∂μ = 1) : ∫⁻ w in s, ‖f w‖ₑ ^ 2 ∂μ = 1 := by
  have hint : Integrable (fun w => ‖f w‖ ^ 2) (μ.restrict s) :=
    Integrable.of_integral_ne_zero (by rw [h]; exact one_ne_zero)
  have e := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun w => by positivity)
  rw [h, ENNReal.ofReal_one] at e
  rw [e]
  refine lintegral_congr fun w => ?_
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem om_vac_eq_smul {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {x : DefSp S}
    {y : DefSp T} (hx : x.Is) (hy : y.Is) {k : KerDat S T} (hk : k.Is ψ θ x y) {z : GA D S} (hz : z ∈ GinfC S) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ k.om (z, 1) k.vac = c • k.vac := by
  obtain ⟨χS, χT, hom⟩ := hk.weil
  obtain ⟨hψ, hv⟩ := hk.vac
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hdet : ∀ τ, (gramAt D S τ).det ≠ 0 := fun τ h0 => by
    have := (hx.cart τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  obtain ⟨r, hr, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ S hdet z hz
  have hy1 : IsDetRoot T 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  have one : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  obtain ⟨a, ha⟩ : ∃ a : ℂ, k.om (z, 1) k.vac = a • k.vac :=
    ⟨_, GlobalTheory.WeilVacChar.vacuum_character D ψ hψ S T θ hθ χS χT k.om η hη hom x.s y.s hx.cart hy.cart z hz 1 (one_mem _)
      (fun τ => by rcases hx.pm τ with h | h <;> rw [h] <;> simp) (fun τ => by rw [one, one_mul, mul_one]) r 1 hr hy1
      k.vac hv.theta hv.fock⟩
  refine ⟨a, ?_, ha⟩
  obtain ⟨⟨p, hp⟩, hn⟩ := hv.norm
  have n1 : nrm2 p.1 p.2 k.vac = 1 := hn p hp
  obtain ⟨hH, hF, -⟩ := hp
  have hu := hom.om_unit p.1 p.2 hH hF (z, 1) k.vac hv.theta
  have hL := lintegral_enorm_sq_eq_one (μ := p.1) (s := p.2) (f := k.vac) n1
  rw [ha] at hu
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow] at hu
  rw [lintegral_const_mul' _ _ (by simp), hL, mul_one] at hu
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_eq_one] at hu
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) two_ne_zero).1 hu

theorem exists_center_char : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ k : KerDat S T, k.Is ψ θ x y → ∃ c : GA D S → ℂ, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ‖c z‖ = 1 ∧ k.om (z, 1) k.vac = c z • k.vac := by
  intro D ψ θ hθ S T x y hx hy k hk
  have h : ∀ z : GA D S, ∃ c : ℂ, z ∈ GinfC S → ‖c‖ = 1 ∧ k.om (z, 1) k.vac = c • k.vac := fun z => by
    by_cases hz : z ∈ GinfC S
    · obtain ⟨c, hc⟩ := om_vac_eq_smul hθ hx hy hk hz
      exact ⟨c, fun _ => hc⟩
    · exact ⟨1, fun h' => absurd h' hz⟩
  choose c hc using h
  exact ⟨c, fun z hz _ => hc z hz⟩

end GlobalTheory.CenterVac
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.PerXCls

variable {D : D7}

abbrev finfF (D : D7) : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem mem_GinfC_iff (V : HSp D) (g : GA D V) : g ∈ GinfC V ↔ (Formalism.L2.Theta.mt V g).map (finfF D) = 1 := by
  show finHom V g = 1 ↔ _
  rw [Units.ext_iff]
  rfl

theorem map_sand {k n : ℕ} (x : Mx D k n) (m : Mx D n n) (y : Mx D n k) (hm : m.map (finfF D) = 1) :
    (x ⬝ m ⬝ y).map (finfF D) = (x ⬝ y).map (finfF D) := by
  have e1 : (x ⬝ m ⬝ y).map (finfF D) = x.map (finfF D) ⬝ m.map (finfF D) ⬝ y.map (finfF D) := by
    rw [Matrix.map_mul (f := finfF D), Matrix.map_mul (f := finfF D)]
  have e2 : (x ⬝ y).map (finfF D) = x.map (finfF D) ⬝ y.map (finfF D) := Matrix.map_mul (f := finfF D)
  rw [e1, e2, hm, Matrix.mul_one]

theorem orth_emb_mem_GinfC {S A B : HSp D} (o : OrthDec S A B) {a : GA D A} (ha : a ∈ GinfC A) :
    o.emb (a, 1) ∈ GinfC S := by
  rw [mem_GinfC_iff] at ha ⊢
  rw [OrthDec.mt_emb, Matrix.map_add _ (map_add (finfF D)), map_sand _ _ _ ha, GlobalTheory.MixModel.mt_one, Matrix.mul_one,
    ← Matrix.map_add _ (map_add (finfF D)), o.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem trc_apply {V : HSp D} (e : GA D V →₀ ℂ) (f : GA D V → ℂ) (x : GA D V) :
    trc e f x = ∑ g ∈ e.support, e g * f (x * g) := by
  simp [trc, rTrans, Finset.sum_apply]

theorem isContAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  have h0 : IsContAut V (0 : GA D V → ℂ) := ⟨fun _ _ _ => rfl, continuous_const⟩
  have hadd : ∀ {f g : GA D V → ℂ}, IsContAut V f → IsContAut V g → IsContAut V (f + g) := fun hf hg =>
    ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩
  have hsm : ∀ {f : GA D V → ℂ}, IsContAut V f → ∀ c : ℂ, IsContAut V (c • f) := fun hf c =>
    ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact hsm ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact hadd hx hy
  | zero => simpa using h0
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact hadd (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact hsm (h x) c

theorem ontoUni_of_reindex {ι K : Type} [Group K] [TopologicalSpace K] {a b : ℕ} (hab : a = b)
    (r : K → ι → Matrix (Fin a) (Fin a) ℂ)
    (hr : OntoUni (fun k τ => (r k τ).reindex (finCongr hab) (finCongr hab))) : OntoUni r := by
  subst hab
  simpa using hr

end GlobalTheory.SeeSaw.PerXCls


open GlobalTheory.SeeSaw.PerXCls in

theorem GlobalTheory.SeeSaw.perX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) →
    ClsPinD t → PerX t := by
  intro D c 𝒯 t hc ht hP
  obtain ⟨ρ, hρ, hA⟩ := hP
  intro n h y v
  have hU : OntoUni (fun k : GinfC c.T => inB c.θ c.T ρ.BT k.1) :=
    ontoUni_of_reindex ρ.hT (fun k : GinfC c.T => inB c.θ c.T ρ.BT k.1) hρ.uniT
  obtain ⟨_, _, _, ν, hν1, hν2, hcls⟩ := integral_eq_classSum D c.θ c.T ρ.BT hc.inf hU
  obtain ⟨hN, hInt, hBr, hne, hblk⟩ := hρ.low n h
  have hemb : ∀ k : GinfC c.T, (c.oT n h).emb (k.1, 1) ∈ GinfC (c.X n) := fun k => orth_emb_mem_GinfC _ k.2
  let y0 : FrN D (ρ.N n) := ρ.fr n y
  have hdet : ∀ (k : GinfC c.T) τ, IsUnit ((ρ.r n h.le ((c.oT n h).emb (k.1, 1)) τ * y0.1 τ).det) := by
    intro k τ
    rw [Matrix.det_mul]
    have hu := (hρ.uni n h.le).uni ⟨_, hemb k⟩ τ
    exact (Matrix.isUnit_det_of_left_inverse (Matrix.mem_unitaryGroup_iff'.mp hu)).mul (y0.2 τ)
  let yk : GinfC c.T → FrN D (ρ.N n) := fun k => ⟨fun τ => ρ.r n h.le ((c.oT n h).emb (k.1, 1)) τ * y0.1 τ, hdet k⟩
  obtain ⟨a, ha⟩ := GlobalTheory.T.unitaryAverage_translate_eq_smul_branchingMap D.what₂.Tau (ρ.N n) ρ.NT hN (fun _ => 1) (fun _ => 1) (ρ.lam n) ρ.sg hInt (ρ.low n h) hBr
    hne (GinfC c.T) ν (fun k => ρ.rT k.1) hρ.uniT y0 yk
    (fun k => ⟨_, fun τ => hblk k.1 k.2 τ, fun τ => rfl⟩) (ρ.J v 1) (hρ.J v).1 (fun k => ρ.J v k.1)
    (fun k z z' hz => (hρ.J v).2 k.1 k.2 z z' hz)
  refine ⟨a, fun s ψ hψ F => ?_⟩
  obtain ⟨⟨A, hA1⟩, B, hB⟩ := hA s
  obtain ⟨hvol, hstab, hsum⟩ := hcls c.volT B.U B.cl B.h hB.reps
  have rdtr := GlobalTheory.T.seesaw_scalar_forms_laws_on_class_data D c (t s) ρ A hc hρ hA1.1 n h.le ψ hψ
  obtain ⟨J, χ, hCT⟩ := (ht s).CT
  have hF : IsContAut c.T (F.1 v) := isContAut_multT (hCT F.2) v
  have key : ∀ β, ∫ h' in c.volT.𝓕, trc ((t s).eT n h β) (F.1 v) h' * (t s).rd n β ψ y ((c.oT n h).emb (h', 1)) ∂c.volT.μ =
      (volLev c.volT B.U : ℂ) * ∑ a', ((stabOrd B.U (B.h a') : ℕ) : ℂ)⁻¹ *
        (a * B.ell n h β a' F (ρ.low n h fun z => (t s).rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (B.h a', 1)))) := by
    intro β
    obtain ⟨hr1, -, hr3, hr4⟩ := rdtr β
    rw [hsum]
    · congr 1
      refine Finset.sum_congr rfl fun a' _ => ?_
      congr 1
      have hpt : ∀ k : GinfC c.T, trc ((t s).eT n h β) (F.1 v) (B.h a' * k.1) *
          (t s).rd n β ψ y ((c.oT n h).emb (B.h a' * k.1, 1)) =
          B.ell n h β a' F (ρ.J v k.1) * (fun z => (t s).rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (B.h a', 1))) (yk k) := by
        intro k
        rw [hB.top n h F v β a' k.1 k.2]
        congr 1
        have hm : (c.oT n h).emb (B.h a' * k.1, 1) = (c.oT n h).emb (B.h a', 1) * (c.oT n h).emb (k.1, 1) := by
          rw [← map_mul]; simp
        rw [hm]
        refine hr3 y _ _ _ (hemb k) ?_
        intro τ
        rw [Equiv.apply_symm_apply]
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact ha _ (hr4 _) _
    · refine Continuous.mul ?_ ((hr1 y).2.comp ((c.oT n h).continuous_emb.comp (continuous_id.prodMk continuous_const)))
      have : trc ((t s).eT n h β) (F.1 v) = fun x => ∑ g ∈ ((t s).eT n h β).support, (t s).eT n h β g * F.1 v (x * g) :=
        funext fun x => trc_apply _ _ x
      rw [this]
      exact continuous_finsetSum _ fun g _ => continuous_const.mul (hF.2.comp (continuous_mul_const g))
    · intro γ hγ g
      rw [trc_apply, trc_apply]
      congr 1
      · refine Finset.sum_congr rfl fun g' _ => ?_
        rw [mul_assoc, hF.1 γ hγ]
      · have hm : (c.oT n h).emb (γ * g, 1) = (c.oT n h).emb (γ, 1) * (c.oT n h).emb (g, 1) := by
          rw [← map_mul]; simp
        rw [hm, (hr1 y).1 _ ((c.oT n h).emb_mem_GQ hγ (GQ _).one_mem)]
    · intro κ hκ g
      exact hB.inv n h ψ hψ F v y β g κ hκ
  have htl := hB.tail n h ψ hψ F
  unfold Tup.perT
  rw [Finset.sum_congr rfl fun β _ => key β]
  calc _ = a * ((volLev c.volT B.U : ℂ) * ∑ β, ∑ a', ((stabOrd B.U (B.h a') : ℕ) : ℂ)⁻¹ *
        B.ell n h β a' F (ρ.low n h fun z => (t s).rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (B.h a', 1)))) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun a' _ => by ring
    _ = _ := by rw [htl]; ring
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem RealD.r_center_scalar {c : Comm D} (ρ : RealD c) (hρ : ρ.Is) (j : ℕ) (hj : j ≤ D.R.m) {z : GA D (c.X j)}
    (hz : z ∈ GinfC (c.X j)) (hzc : z ∈ Subgroup.center (GA D (c.X j))) (τ : D.what₂.Tau) :
    ρ.r j hj z τ = (Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) • (1 : Matrix (Fin (ρ.N j)) (Fin (ρ.N j)) ℂ) := by
  have hu := hρ.uni j hj
  obtain ⟨ζ, hζ⟩ := GlobalTheory.CenterScalar.scalar_of_comm_unitary (ρ.r j hj z τ) fun U hU => by
    obtain ⟨k, hk⟩ := hu.onto (fun _ => U) fun _ => (Matrix.mem_unitaryGroup_iff').2 hU
    have e1 := hu.mul k ⟨z, hz⟩ τ
    have e2 := hu.mul ⟨z, hz⟩ k τ
    have hkz : (k * ⟨z, hz⟩ : GinfC (c.X j)) = ⟨z, hz⟩ * k :=
      Subtype.ext ((Subgroup.mem_center_iff.1 hzc) k.1)
    rw [hkz, e2] at e1
    have hk' : ρ.r j hj k.1 τ = U := congrFun hk τ
    rw [hk'] at e1
    exact e1.symm
  rcases Nat.eq_zero_or_pos (ρ.N j) with h0 | hpos
  · ext a
    exact absurd a.2 (by omega)
  · rw [hζ, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
      mul_div_assoc, div_self (by exact_mod_cast hpos.ne'), mul_one]

theorem rdX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → RdX t := by
  intro D c 𝒯 t hc _ hP j hj
  obtain ⟨ρ, hρ, H⟩ := hP
  refine ⟨fun z => ∏ τ, (Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) ^ (∑ i, (ρ.lam j τ).w i), fun s ψ hψ α y => ?_⟩
  obtain ⟨⟨A, hA⟩, -⟩ := H s
  obtain ⟨h1, -, h3, h4⟩ := GlobalTheory.T.seesaw_scalar_forms_laws_on_class_data D c (t s) ρ A hc hρ hA.1 j hj ψ hψ α
  refine ⟨h1 y, fun z hz hzc g => ?_⟩
  have hdet : ∀ τ, IsUnit (ρ.r j hj z τ).det := fun τ =>
    Matrix.isUnit_det_of_left_inverse ((Matrix.mem_unitaryGroup_iff').1 ((hρ.uni j hj).uni ⟨z, hz⟩ τ))
  set w := (ρ.fr j y).tr (ρ.r j hj z) hdet with hw
  have e1 : (t s).rd j α ψ y (g * z) = (t s).rd j α ψ ((ρ.fr j).symm w) g :=
    h3 y _ g z hz (by rw [Equiv.apply_symm_apply]; exact Frames.isTr_tr _ hdet _)
  have e2 := (GlobalTheory.KJInf.valC_poly _ _ _ _ |>.2.2.2) _ (h4 g) (fun τ => Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) (ρ.fr j y) w
    (fun τ => by
      show ρ.r j hj z τ * (ρ.fr j y).1 τ = _
      conv_lhs => rw [ρ.r_center_scalar hρ j hj hz hzc τ]
      rw [Matrix.smul_mul, Matrix.one_mul])
  simp only [Equiv.symm_apply_apply] at e2
  rw [e1, e2]

end GlobalTheory.SeeSaw
end
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces : ∀ D : D7, GlobalTheory.FinPl.LatAll D := by
  first | exact @GlobalTheory.LatPresc.latAll | exact GlobalTheory.LatPresc.latAll | (intros; apply GlobalTheory.LatPresc.latAll <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.KJRealOnb

variable {D : D7}

theorem det_ne_zero_of_onb {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (hG : IsCartanInv G 1)
    (hB : ∃ p, IsONBasis G 1 B p) : G.det ≠ 0 ∧ B.det ≠ 0 := by
  have hP : G.PosDef := by simpa using hG.2.2
  have hGd : G.det ≠ 0 := hP.det_pos.ne'
  refine ⟨hGd, fun h0 => ?_⟩
  obtain ⟨p, ε, hε, h1, -⟩ := hB
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at h2
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h2.symm
  rcases hε a with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

theorem det_inB (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V)
    (τ : D.what₂.Tau) (hB : (B τ).det ≠ 0) : (inB θ V B g τ).det = (compAt θ τ (mt V g)).det := by
  unfold inB
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hB), Matrix.det_one, one_mul]

theorem comp_eq_mul_inB (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V)
    (hB : ∀ τ, (B τ).det ≠ 0) : (fun τ => compAt θ τ (mt V g) * B τ) = fun τ => B τ * inB θ V B g τ := by
  funext τ
  unfold inB
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit (hB τ)), Matrix.one_mul]

end GlobalTheory.KJRealOnb

namespace GlobalTheory.KJReal


open GlobalTheory.KJRealOnb in
theorem om_pureTensorO_onb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (x : DefSp S) (y : DefSp T) (μ : (AE D)ˣ →* Circle) (om : Om S T), IsInfFam θ → x.Is → y.Is → x.s = (fun _ => 1) → y.s = (fun _ => 1) → Even S.rank → Even T.rank → IsWeilDatumO ψ S T μ μ om → ∀ e : D.what₂.Tau → ℤ, (∀ τ, HasInfExp D μ τ (e τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) → ∀ k ∈ GinfC S, ∀ k' ∈ GinfC T, ∀ P, om (k, k') (pureTensorO ψ θ S T x.s y.s x.B y.B f P) = (∏ τ, (inB θ S x.B k τ).det ^ (-e τ - T.rank / 2 : ℤ) * (inB θ T y.B k' τ).det ^ (e τ + S.rank / 2 : ℤ)) • pureTensorO ψ θ S T x.s y.s x.B y.B f (mvZ (fun τ => (inB θ S x.B k τ)⁻¹) (inB θ T y.B k') P) := by
  intro D ψ θ S T x y μ om hθ hx hy hxs hys eS eT hom e he f hf hv k hk k' hk' P
  obtain ⟨mS, hmS⟩ := eS
  obtain ⟨mT, hmT⟩ := eT
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hψ := hom.std
  have cS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => by have h := hx.cart τ; rw [hxs] at h; exact h
  have cT : ∀ τ, IsCartanInv (gramAt D T τ) 1 := fun τ => by have h := hy.cart τ; rw [hys] at h; exact h
  have dS : ∀ τ, (gramAt D S τ).det ≠ 0 ∧ (x.B τ).det ≠ 0 := fun τ =>
    det_ne_zero_of_onb (cS τ) (by have h := hx.onb τ; rw [hxs] at h; exact h)
  have dT : ∀ τ, (gramAt D T τ).det ≠ 0 ∧ (y.B τ).det ≠ 0 := fun τ =>
    det_ne_zero_of_onb (cT τ) (by have h := hy.onb τ; rw [hys] at h; exact h)
  obtain ⟨xr, hxr, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (fun τ => (dS τ).1) k hk
  obtain ⟨yr, hyr, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (fun τ => (dT τ).1) k' hk'
  have hvac := GlobalTheory.WeilVacChar.vacuum_character D ψ hψ S T θ hθ μ μ om η hη hom (fun _ => 1) (fun _ => 1)
    cS cT k hk k' hk' (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) xr yr hxr hyr f hf hv
  have expT : ∀ τ, HasInfExp D (μ * (η ^ T.rank)⁻¹) τ ((e τ - mT : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (he τ) (hη.2.2.2 τ) T.rank
    convert h1 using 1
    rw [hmT]; push_cast; ring
  have expS : ∀ τ, HasInfExp D (μ * (η ^ S.rank)⁻¹) τ ((e τ - mS : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (he τ) (hη.2.2.2 τ) S.rank
    convert h1 using 1
    rw [hmS]; push_cast; ring
  have vx := hxv _ (fun τ => e τ - mT) expT
  have vy := hyv _ (fun τ => e τ - mS) expS
  have hmain := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T μ μ om hom hθ (fun _ => 1) (fun _ => 1) x.B
    (fun τ => compAt θ τ (mt S k) * x.B τ) (fun _ => 1) (fun _ => 1) y.B
    (fun τ => compAt θ τ (mt T k') * y.B τ) k k' (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => rfl) (fun τ => rfl) f hf P).2
  rw [hxs, hys, hmain, hvac, GlobalTheory.FiniteFock.pureTensorO_smul, comp_eq_mul_inB θ S x.B k (fun τ => (dS τ).2),
    comp_eq_mul_inB θ T y.B k' (fun τ => (dT τ).2),
    GlobalTheory.FockBaseChange.pureTensorO_subst D ψ θ S T hψ hθ x.B (inB θ S x.B k) y.B (inB θ T y.B k') f hf P]
  congr 1
  · rw [Circle.coe_mul, Circle.coe_inv, vx, vy, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have inv := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k)
    rw [Matrix.det_mul, Matrix.det_one] at inv
    have g0 := left_ne_zero_of_mul_eq_one inv
    have inv' := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k')
    rw [Matrix.det_mul, Matrix.det_one] at inv'
    have g0' := left_ne_zero_of_mul_eq_one inv'
    rw [GlobalTheory.KJReal.detPlus_one_one, eq_inv_of_mul_eq_one_right inv, det_inB θ S x.B k τ (dS τ).2,
      det_inB θ T y.B k' τ (dT τ).2]
    have a1 : -e τ - (T.rank : ℤ) / 2 = -e τ - mT := by omega
    have a2 : e τ + (S.rank : ℤ) / 2 = e τ + mS := by omega
    rw [a1, a2]
    exact GlobalTheory.KJReal.exp_identity _ _ g0 g0' (e τ) mS mT S.rank T.rank (by rw [hmS]; push_cast; ring)
      (by rw [hmT]; push_cast; ring)

end GlobalTheory.KJReal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

theorem _root_.GlobalTheory.T.weilOperator_thetaFun_sup_moderate_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ g h w, ‖om (g, h) f w‖ ≤ C * (height S g * height T h) ^ A := by
  first | exact @GlobalTheory.SupThetaGrowth.om_sup_growth | exact GlobalTheory.SupThetaGrowth.om_sup_growth | (intros; apply GlobalTheory.SupThetaGrowth.om_sup_growth <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens


theorem _root_.GlobalTheory.T.thetaFunctions_open_level_complete_sobolev : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ _root_.GlobalTheory.Size.thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∃ f ∈ _root_.GlobalTheory.Size.thetaLevel ψ S T U, ∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.ThetaComplete.complete | exact GlobalTheory.ThetaComplete.complete | (intros; apply GlobalTheory.ThetaComplete.complete <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

theorem _root_.GlobalTheory.T.stdChar_annihilator_openSubgroup_finPart_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (AE D), IsOpen (U : Set (AE D)) → ∃ K : Set (AE D), IsCompact K ∧ ∀ x : AE D, (∀ a ∈ U, infPart D a = 0 → ψ (Algebra.trace (AF D.host.F) (AE D) (x * a)) = 1) → ∃ k ∈ K, finPart D (x - k) = 0 := by
  first | exact @GlobalTheory.CondBound.annihilator_finPart_compact | exact GlobalTheory.CondBound.annihilator_finPart_compact | (intros; apply GlobalTheory.CondBound.annihilator_finPart_compact <;> assumption)
end
