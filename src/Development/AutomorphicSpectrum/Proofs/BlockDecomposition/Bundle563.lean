module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle434
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle547
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle557
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT

@[expose] public section

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CompanionTheory.AnisoRange

theorem bddAbove_isotropic_dims {D : D7} (V : HSp D) :
    BddAbove {k | ∃ W : Submodule D.host.E V.V, Module.finrank D.host.E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, V.hT x y = 0} := by
  haveI := V.fd
  refine ⟨Module.finrank D.host.E V.V, ?_⟩
  rintro k ⟨W, rfl, -⟩
  exact Submodule.finrank_le W

theorem one_le_wittIdx {D : D7} (V : HSp D) {v : V.V} (hv : v ≠ 0) (h : V.hT v v = 0) :
    1 ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  refine le_csSup (bddAbove_isotropic_dims V) ⟨Submodule.span D.host.E {v}, finrank_span_singleton hv, ?_⟩
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
  simp [h]

theorem hT_coord {D : D7} (V : HSp D) (x : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm x) =
      HeckeCharacterZeroLocus.SiegelWeilU.hE D.sp.cm.sig (HSpace.gram V) x x := by
  have hσ : ∀ a : D.host.E, ((D.sp.cm.sig : D.host.E →ₐ[D.host.F] D.host.E) : D.host.E →+* D.host.E) a = star a :=
    fun _ => rfl

  simp only [Module.Basis.equivFun_symm_apply, HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, map_sum, LinearMap.sum_apply,
  map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hσ, HSpace.gram]
  simp only [starRingEnd_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.id_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem anisoOfRange : PositivityTheory.PfSWUS.AnisoOfRange := by
  rintro D n V ⟨h1, -, h3⟩
  by_cases h : n + 2 ≤ V.rank
  · exact Or.inl h
  refine Or.inr fun x hx => ?_
  by_contra hne
  have hv : V.frame.equivFun.symm x ≠ 0 := fun h0 => hne ((map_eq_zero_iff _ V.frame.equivFun.symm.injective).1 h0)
  have := one_le_wittIdx V hv ((hT_coord V x).trans hx)
  omega

end GlobalTheory.CompanionTheory.AnisoRange
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.IwaAd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

theorem data_zero_of_data {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
    {bs : Module.Basis (Fin d) F E} {ψ} {ι : Type} [Fintype ι] {θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν}
    (h : PositivityTheory.SiegelWeilFormula.Gen.Dat (ι := ι) σ J T bs ψ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν) :
    PositivityTheory.SiegelWeilFormula.Gen.Dat0 (ι := ι) σ J T bs ψ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν :=
  { cm := h.cm, herm := h.herm, hT := h.hT, det := h.det, chr := h.chr, places := h.places,
    frames := h.frames, haar := h.haar, co := h.co, std := h.std, pure := h.pure, prod := h.prod,
    sdW := h.sdW, sdH := h.sdH }

theorem whitKAOfGenLt : PositivityTheory.PfSWUS.WhitKAOfGenLt := by
  intro hGen hDict hAn D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨N, φs, vals, ⟨t, ht⟩, hv, hm⟩ := hDict D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν hS.hν
  have key : ∀ j, HolValueAt (whitT ψ V μ lam nb w H (φs j) (adj a.1 * β.1.map (incA D) * a.1) k) (s0 V n) (vals j) := by
    intro j
    obtain ⟨d, bs, θG, lG, εG, frG, gG, PG, lamG, L₁, L₂, ΦG, Φf, Φv, μG, νG, ψG, hDat, C, ⟨t', ht'⟩, hval⟩ := hm j
    have h := hGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (data_zero_of_data hDat) hDat.lt (hAn D n V hR) False.elim
      ⟨t', fun z hz => (ht' z hz).1⟩ ν 𝓕 hS.hν h𝓕
    have e : ((V.rank : ℂ) - n) / 2 = s0 V n := by
      simp only [s0]
      ring
    rw [hval ν 𝓕 hS.hν h𝓕]
    rw [one_mul] at h
    have h2 := (holValueAt_const C _).mul h
    rw [e] at h2
    exact h2.congr ⟨t', fun z hz => ((ht' z hz).2).symm⟩
  rw [hv]
  exact (holValueAt_finset_sum Finset.univ fun j _ => key j).congr ⟨t, fun z hz => (ht z hz).symm⟩

end GlobalTheory.CompanionTheory.IwaAd

end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.NuGalSquare

theorem cr_square_semi {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1}
    {h₃ : b₃.t = 1} {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I}
    {κ₄ : O →+* b₄.R ⧸ b₄.I} {Λ : Type} [CommRing Λ] {c₁ : Λ →+* b₁.R} {c₂ : Λ →+* b₂.R} {c₃ : Λ →+* b₃.R} {c₄ : Λ →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R} {τa τb τc τd : Λ →+* Λ}
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τa a)) (hb : ∀ a, σb (c₂ a) = c₄ (τb a)) (hc : ∀ a, σc (c₁ a) = c₃ (τc a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τd a)) (hτ : τb.comp τa = τd.comp τc) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (x : CH.H (B.OM (F₁.cr b₁ h₁ κ₁) c₁) j) :
    (B.omMor (c := c₂) (c' := c₄) mb τb hb).pull j ((B.omMor (c := c₁) (c' := c₂) ma τa ha).pull j x) =
      (B.omMor (c := c₃) (c' := c₄) md τd hd).pull j ((B.omMor (c := c₁) (c' := c₃) mc τc hc).pull j x) := by
  haveI t₁ : RingHomCompTriple τa τb (τb.comp τa) := ⟨rfl⟩
  haveI t₂ : RingHomCompTriple τc τd (τb.comp τa) := ⟨hτ.symm⟩
  rw [pull_pull (τb.comp τa), pull_pull (τb.comp τa)]
  exact cr_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem commute_phi_gal (σ : Gal(PadicAlgCl l/K)) : Commute (ACris.phi (K := ℂ_[l]) (p := l)) (ACris.galCris σ) :=
  RingHom.ext fun a => ACris.phi_gal_smul σ a

theorem phiA_comp_gal (σ : Gal(PadicAlgCl l/K)) (N : ℕ) :
    (Mid.phiA l N).comp (ACris.galCris σ) = (ACris.galCris σ).comp (Mid.phiA l N) :=
  ((commute_phi_gal σ).pow_left N).eq

theorem commute_phi_galBase (σ : Gal(PadicAlgCl l/K)) (n : ℕ) : Commute ((base l).phi n) (galBase σ n) :=
  RingHom.ext fun r => by
    obtain ⟨a, rfl⟩ := (RL.base_acr (base l) isBase_base).2 n |>.1 r
    change (base l).phi n (galBase σ n ((base l).cris n a)) = galBase σ n ((base l).phi n ((base l).cris n a))
    rw [galBase_cris, (base l).phi_cris, (base l).phi_cris, galBase_cris]
    exact congrArg _ (ACris.phi_gal_smul σ a)

theorem phiP_galBase (σ : Gal(PadicAlgCl l/K)) (n N : ℕ) (x : (base l).Acr n) :
    Mid.phiP l n N (galBase σ n x) = galBase σ n (Mid.phiP l n N x) :=
  RingHom.congr_fun ((commute_phi_galBase σ n).pow_left N).eq x

theorem nu_gal : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j), Mid.nu r M n j hT (B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j x) = galM r M σ hσ n j (Mid.nu r M n j hT x) := by
  intro l _ K r N hT M σ hσ n j x
  exact cr_square_semi
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (B.gal_κb (okToOC l K) σ (galOC_okToOC σ) true n)) fun _ _ _ => rfl)
    (Mid.mOut r M n hT) (Mid.mOut r M n hT)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (gal_κm r σ hσ n)) fun _ _ _ => rfl)
    (galBase_cris σ n) (Mid.phiP_cris n N) (Mid.phiP_cris n N) (galBase_cris σ n)
    (phiA_comp_gal σ N) (phiP_galBase σ n N) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.NuGalSquare
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.MuGal

private theorem cr_square_same_base {O : Type} [CommRing O] {F : B.Fn O} {b : Base}
    {h : b.t = 1} {κm κb : O →+* b.R ⧸ b.I} {Λ : Type} [CommRing Λ] {c : Λ →+* b.R}
    {g : b.R →+* b.R} {τ : Λ →+* Λ}
    (ma : Mor (F.cr b h κm) (F.cr b h κm) g)
    (m : Mor (F.cr b h κm) (F.cr b h κb) (RingHom.id b.R))
    (md : Mor (F.cr b h κb) (F.cr b h κb) g)
    (hg : ∀ a, g (c a) = c (τ a))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F.cr b h κb).Pt.obj B₀),
      (ma.pt.app B₀ (m.pt.app B₀ y)).1.2 = (m.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (t : CH.H (B.OM (F.cr b h κm) c) j) :
    (B.omMor (c := c) (c' := c) md τ hg).pull j
        ((B.omMor (c := c) (c' := c) m (RingHom.id Λ) (fun _ => rfl)).pull j t) =
      (B.omMor (c := c) (c' := c) m (RingHom.id Λ) (fun _ => rfl)).pull j
        ((B.omMor (c := c) (c' := c) ma τ hg).pull j t) :=
  (cr_square ma m m md hg (fun _ => rfl) (fun _ => rfl) hg (fun _ => rfl) hpt j t).symm

theorem mu_gal {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (t : Mid.HM r M n j) :
    B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j (Mid.mu r M n j hT t) = Mid.mu r M n j hT (galM r M σ hσ n j t) := by
  let F := B.schFn M.p
  let b := B.bs l true n
  let κm := Mid.κm r n
  let κb := B.κb (okToOC l K) true n
  let g := galBase σ n
  let c := (base l).cris n
  let ma := B.crMor (F := F) (F' := F) (b := b) (b' := b) (ht := rfl) (ht' := rfl)
    (κ := κm) (κ' := κm) g rfl (B.dd_gal true σ n)
    (B.basePt F _ (gal_κm r σ hσ n)) fun _ _ _ => rfl
  let md := B.crMor (F := F) (F' := F) (b := b) (b' := b) (ht := rfl) (ht' := rfl)
    (κ := κb) (κ' := κb) g rfl (B.dd_gal true σ n)
    (B.basePt F _ (B.gal_κb (okToOC l K) σ (galOC_okToOC σ) true n)) fun _ _ _ => rfl
  refine cr_square_same_base (O := OK l K) (F := F) (b := b) (h := rfl) (κm := κm) (κb := κb)
    (Λ := Acris l) (c := c) (g := g) (τ := ACris.galCris σ)
    ma (Mid.mIn r M n hT) md (galBase_cris σ n) ?_ j t
  intro B₀ y
  -- Give the kernel the common point explicitly, before either composite is unfolded.
  exact Eq.refl (F.Pt.map (CommRingCat.ofHom (Mid.frbN (Mid.l_zero y.1.1) N)) y.1.2)

end GlobalTheory.CompanionTheory.MuGal
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrysMid

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

noncomputable def trueRed (M : Model l K) (n : ℕ) :
    Mor (B.Lc (B.schFn M.p) (okToOC l K) true (n + 1)) (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).red (Nat.le_succ n)) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true (n + 1)) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).red (Nat.le_succ n)) rfl (B.dd_red true _ (Nat.le_succ n))
      (B.basePt _ _ (B.red_κb (okToOC l K) true (Nat.le_succ n))) fun _ _ _ => rfl

noncomputable def midRed (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n : ℕ) :
    Mor (Mid.Lm r M (n + 1)) (Mid.Lm r M n) ((base l).red (Nat.le_succ n)) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true (n + 1)) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).red (Nat.le_succ n)) rfl (B.dd_red true _ (Nat.le_succ n))
      (B.basePt _ _ (red_κm r (Nat.le_succ n))) fun _ _ _ => rfl

theorem ptIn_val (F : B.Fn (OK l K)) {r : CrystallineSemistableComparison.Res l K} {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (n : ℕ) (B₀ : CommRingCat.{0})
    (y : (F.ptK (B.κb (okToOC l K) true n)).obj B₀) (h : (l : B₀) = 0) :
    ((Mid.ptIn F n hT).app B₀ y).1.2 = F.Pt.map (CommRingCat.ofHom (Mid.frbN h N)) y.1.2 := rfl

theorem base_val {O : Type} [CommRing O] (F : B.Fn O) {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] {κ₁ : O →+* k₁} {κ₂ : O →+* k₂}
    (τ : k₁ →+* k₂) (h : τ.comp κ₁ = κ₂) (B₀ : CommRingCat.{0}) (y : (F.ptK κ₂).obj B₀) :
    ((B.basePt F τ h).app B₀ y).1.2 = y.1.2 := rfl

theorem ptIn_base (F : B.Fn (OK l K)) (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (n : ℕ) (B₀ : CommRingCat.{0})
    (y : (F.ptK (B.κb (okToOC l K) true n)).obj B₀) :
    ((Mid.ptIn F (n + 1) hT).app B₀ ((B.basePt F _ (B.red_κb (okToOC l K) true (Nat.le_succ n))).app B₀ y)).1.2 =
      ((B.basePt F _ (red_κm r (Nat.le_succ n))).app B₀ ((Mid.ptIn F n hT).app B₀ y)).1.2 := by
  have h : (l : B₀) = 0 := Mid.l_zero y.1.1
  rw [ptIn_val F hT (n + 1) B₀ _ h, base_val, base_val, ptIn_val F hT n B₀ _ h]

theorem pt_sq (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n : ℕ) (B₀ : CommRingCat.{0})
    (y : (B.Lc (B.schFn M.p) (okToOC l K) true n).Pt.obj B₀) :
    ((Mid.mIn r M (n + 1) hT).pt.app B₀ ((trueRed M n).pt.app B₀ y)).1.2 =
      ((midRed r M n).pt.app B₀ ((Mid.mIn r M n hT).pt.app B₀ y)).1.2 :=
  ptIn_base (B.schFn M.p) r hT n B₀ y

theorem mid_square (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j) :
    (B.omMor (c := (base l).cris (n + 1)) (c' := (base l).cris n) (trueRed M n) (RingHom.id _) (B.red_cris _ (Nat.le_succ n))).pull j
      ((B.omMor (c := (base l).cris (n + 1)) (c' := (base l).cris (n + 1)) (Mid.mIn r M (n + 1) hT) (RingHom.id _) (Wc.idc _)).pull j t) =
    (B.omMor (c := (base l).cris n) (c' := (base l).cris n) (Mid.mIn r M n hT) (RingHom.id _) (Wc.idc _)).pull j
      ((B.omMor (c := (base l).cris (n + 1)) (c' := (base l).cris n) (midRed r M n) (RingHom.id _) (B.red_cris _ (Nat.le_succ n))).pull j t) :=
  cr_square (F₁ := B.schFn M.p) (F₂ := B.schFn M.p) (F₃ := B.schFn M.p) (F₄ := B.schFn M.p)
    (b₁ := B.bs l true (n + 1)) (b₂ := B.bs l true (n + 1)) (b₃ := B.bs l true n) (b₄ := B.bs l true n)
    (h₁ := rfl) (h₂ := rfl) (h₃ := rfl) (h₄ := rfl)
    (κ₁ := Mid.κm r (n + 1)) (κ₂ := B.κb (okToOC l K) true (n + 1)) (κ₃ := Mid.κm r n) (κ₄ := B.κb (okToOC l K) true n)
    (Λ := Acris l) (c₁ := (base l).cris (n + 1)) (c₂ := (base l).cris (n + 1)) (c₃ := (base l).cris n)
    (c₄ := (base l).cris n) (τ := RingHom.id _)
    (Mid.mIn r M (n + 1) hT) (trueRed M n) (midRed r M n) (Mid.mIn r M n hT)
    (Wc.idc _) (B.red_cris _ (Nat.le_succ n)) (B.red_cris _ (Nat.le_succ n)) (Wc.idc _) (fun x => (Wc.idc ((base l).red (Nat.le_succ n)) x).symm)
    (pt_sq r hT M n) j t

theorem mu_redHc (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j) :
    B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j (Mid.mu r M (n + 1) j hT t) = Mid.mu r M n j hT ((redT r M (Nat.le_succ n)).pull j t) :=
  mid_square r hT M n j t

end GlobalTheory.CompanionTheory.CrysMid
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.NuPhi

theorem cr_square_semi {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1} {h₃ : b₃.t = 1}
    {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I} {κ₄ : O →+* b₄.R ⧸ b₄.I}
    {Λ : Type} [CommRing Λ] {c₁ : Λ →+* b₁.R} {c₂ : Λ →+* b₂.R} {c₃ : Λ →+* b₃.R} {c₄ : Λ →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R} {τa τb τc τd : Λ →+* Λ} (τ : Λ →+* Λ)
    [RingHomCompTriple τa τb τ] [RingHomCompTriple τc τd τ]
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τa a)) (hb : ∀ a, σb (c₂ a) = c₄ (τb a)) (hc : ∀ a, σc (c₁ a) = c₃ (τc a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τd a)) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (x : CH.H (B.OM (F₁.cr b₁ h₁ κ₁) c₁) j) :
    (B.omMor (c := c₂) (c' := c₄) mb τb hb).pull j ((B.omMor (c := c₁) (c' := c₂) ma τa ha).pull j x) =
      (B.omMor (c := c₃) (c' := c₄) md τd hd).pull j ((B.omMor (c := c₁) (c' := c₃) mc τc hc).pull j x) := by
  rw [pull_pull τ, pull_pull τ]
  exact cr_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

variable {l : ℕ} [Fact l.Prime]

instance tripleL (N : ℕ) : RingHomCompTriple (ACris.phi (K := ℂ_[l]) (p := l)) (Mid.phiA l N) (Mid.phiA l (N + 1)) :=
  ⟨by
    have e : Mid.phiA l (N + 1) = Mid.phiA l N * ACris.phi (K := ℂ_[l]) (p := l) := pow_succ _ _
    rw [e]; rfl⟩

instance tripleR (N : ℕ) : RingHomCompTriple (Mid.phiA l N) (ACris.phi (K := ℂ_[l]) (p := l)) (Mid.phiA l (N + 1)) :=
  ⟨by
    have e : Mid.phiA l (N + 1) = ACris.phi (K := ℂ_[l]) (p := l) * Mid.phiA l N := pow_succ' _ _
    rw [e]; rfl⟩

theorem phiP_phi (n N : ℕ) (x : (base l).Acr n) :
    Mid.phiP l n N ((base l).phi n x) = (base l).phi n (Mid.phiP l n N x) := by
  have e : Mid.phiP l n (N + 1) = Mid.phiP l n N * (base l).phi n := pow_succ _ _
  rw [← Mid.phiP_succ, e]; rfl

theorem nu_phi {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.phiHc (B.schFn M.p) (okToOC l K) n j x) = phiM r M n j (Mid.nu r M n j hT x) := by
  exact cr_square_semi (Mid.phiA l (N + 1))
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl) ((base l).phi n) rfl
      ((base l).dpP_phi n) (B.phiPt (B.schFn M.p) (okToOC l K) n) fun _ y r =>
        ((congrArg y.1.1 (B.phi_mk (base l) n r)).trans (map_pow y.1.1 _ l)).symm)
    (Mid.mOut r M n hT)
    (Mid.mOut r M n hT)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).phi n) rfl ((base l).dpP_phi n) (phiPtT _ n _) fun _ y r =>
        ((congrArg y.1.1 (B.phi_mk (base l) n r)).trans (map_pow y.1.1 _ l)).symm)
    ((base l).phi_cris n) (Mid.phiP_cris n N) (Mid.phiP_cris n N) ((base l).phi_cris n)
    (fun x => (phiP_phi n N x)) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.NuPhi
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.NuPull

theorem nu_pull {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ}
    (hT : Mid.TeichmullerCongruence r N) {M M' : Model l K} (u : M.X ⟶ M'.X) (hu : u ≫ M'.p = M.p) (n j : ℕ)
    (x : B.Hc (B.schFn M'.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.pullHc (okToOC l K) (B.schMap u hu) true n j x) = pullM r u hu n j (Mid.nu r M' n j hT x) := by
  unfold Mid.nu pullM B.pullHc Mid.nuMor pullT' B.pullMorC
  exact (cr_square (Mid.mOut r M' n hT)
    (B.crMor (F := B.schFn M'.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (RingHom.id _) rfl (DPMorphism.id _).isDPMorphism ((B.schMap u hu).ptK _) fun _ _ _ => rfl)
    (B.crMor (F := B.schFn M'.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (RingHom.id _) rfl (DPMorphism.id _).isDPMorphism ((B.schMap u hu).ptK _) fun _ _ _ => rfl)
    (Mid.mOut r M n hT)
    (Mid.phiP_cris n N) (fun _ => rfl) (fun _ => rfl) (Mid.phiP_cris n N) (fun _ => rfl) (fun _ _ => rfl) j x).symm

end GlobalTheory.CompanionTheory.NuPull
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.NuRed

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem red_phiP {m n : ℕ} (h : n ≤ m) (N : ℕ) (x : (base l).Acr m) :
    (base l).red h (Mid.phiP l m N x) = Mid.phiP l n N ((base l).red h x) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Mid.phiP_succ, Mid.phiP_succ, ← ih]; exact (pdOk_frob _).red_acr h _

def redLm (r : CrystallineSemistableComparison.Res l K) (M : Model l K) {m n : ℕ} (h : n ≤ m) :
    Mor (Mid.Lm r M m) (Mid.Lm r M n) ((base l).red h) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true m) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    ((base l).red h) rfl (B.dd_red true _ h) (B.basePt _ _ (red_κm r h)) fun _ _ _ => rfl

def redLc (M : Model l K) {m n : ℕ} (h : n ≤ m) :
    Mor (B.Lc (B.schFn M.p) (okToOC l K) true m) (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).red h) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true m) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    ((base l).red h) rfl (B.dd_red true _ h) (B.basePt _ _ (B.red_κb _ true h)) fun _ _ _ => rfl

theorem ptOut_snd (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (F : B.Fn (OK l K)) (n : ℕ)
    (B₀ : CommRingCat.{0}) (y : (F.ptK (Mid.κm r n)).obj B₀) :
    ((Mid.ptOut F n hT).app B₀ y).1.2 = y.1.2 := rfl

theorem nu_pt (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (F : B.Fn (OK l K)) {m n : ℕ} (h : n ≤ m)
    (B₀ : CommRingCat.{0}) (y : (F.ptK (Mid.κm r n)).obj B₀) :
    ((Mid.ptOut F m hT).app B₀ ((B.basePt F _ (red_κm r h)).app B₀ y)).1.2 =
      ((B.basePt F _ (B.red_κb _ true h)).app B₀ ((Mid.ptOut F n hT).app B₀ y)).1.2 := by
  rw [ptOut_snd, SH.base_snd, SH.base_snd, ptOut_snd]

theorem nu_red : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ}
    (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true (n + 1) j),
    (redT r M (Nat.le_succ n)).pull j (Mid.nu r M (n + 1) j hT x) =
      Mid.nu r M n j hT (B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j x) := by
  intro l _ K r N hT M n j x
  unfold Mid.nu Mid.nuMor B.redHc B.redMor redT
  exact cr_square (Mid.mOut r M (n + 1) hT) (redLm r M (Nat.le_succ n)) (redLc M (Nat.le_succ n)) (Mid.mOut r M n hT)
    (Mid.phiP_cris _ N) (B.red_cris _ (Nat.le_succ n)) (B.red_cris _ (Nat.le_succ n)) (Mid.phiP_cris _ N)
    (red_phiP (Nat.le_succ n) N) (nu_pt r hT _ (Nat.le_succ n)) j x

end GlobalTheory.CompanionTheory.NuRed
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

theorem _root_.GlobalTheory.T.existsUnique_chern_class_nilpotent_base : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ]
    (c : Λ →+* R) (N : ℕ), (N.factorial : R) = 0 →
    ∃! x, B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D c N x := by
  first | exact @GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class | exact GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class | (intros; apply GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

theorem _root_.GlobalTheory.T.cofinite_of_capelli_monic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (J : Set (Module.End ℂ (Sm E n))), J ⊆ Zalg E n → (∀ (τ : E →+* ℂ) (u : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ Polynomial.aeval (cap (a := n) τ u) q ∈ J) → Cofin J := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic | exact GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic | (intros; apply GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic <;> assumption)
end
