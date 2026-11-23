module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle467
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle240
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle389
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle744
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle714
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle485
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle444
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle462
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle119
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle048
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle080
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle067
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExhaustionOfThree
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
import GroundTheory.LocalFields.PadicLogSeries
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic

@[expose] public section

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
namespace GlobalTheory.CompanionTheory.IwaAd
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
variable {D : D7} {n : ℕ}


theorem whit_step (hK : WhitKA) {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {Φ : schwartzA θ V.rank n} (hS : Std D n V ψ χ θ μ ω H l s ν Φ) (hR : InRange V n)
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} {nb : hermA D n → G D n} (hC : CoefData nb lam 𝓖)
    {w : G D n} (hw : mat w = blk4 0 1 (-1) 0) {β : HermE D n} (hβ : β.1.det ≠ 0)
    (a : GL (Fin n) (AE D)) {m u k : G D n} (hk : k ∈ K D n) (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1))
    (b1 : hermA D n) (hu : mat u = blk4 1 b1.1 0 1) :
    HolValueAt (fun z => ∫ b, npow (H (w * nb b * (m * u * k))) (z - s0 V n) * Jt ψ V μ (ω (m * u * k) Φ).1 b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam)
      (s0 V n) (IfrB V ν (ω (m * u * k) Φ).1 β) := by
  have hω := hS.hω
  have hH := hS.hH
  obtain ⟨𝓕, h𝓕⟩ := hS.hμ
  have hμ : μ.IsAddHaarMeasure := h𝓕.1
  have hl : lam.IsAddHaarMeasure := hC.2.1
  have hnb : IsNMap nb := hC.1
  have hub : u = nb b1 := mat_inj (by rw [hnb b1]; exact hu)
  set A := absA D (Matrix.GeneralLinearGroup.det a) with hAdef
  have hA : 0 < A := absA_pos _
  obtain ⟨m', hm'P, hm'⟩ := exists_ad a
  have hwm : w * m = m' * w := weyl_mul hw a hm hm'
  have hblk : blkA (mat m') = (ad a).1 := by rw [hm', upperLeft_blockMatrix]; rfl
  set φ0 : schwartzA θ V.rank n := ω k Φ with hφ0
  have hωe : ω (m * u * k) Φ = ω (m * u) φ0 := by
    rw [map_mul (f := ω) (m * u) k]; rfl
  set T : Mx D n n := adj a.1 * β.1.map (incA D) * a.1 with hT
  set ct : ℂ := ψ (halfTr (Matrix.trace (T * b1.1))) with hct
  set c0 : ℂ := (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow A ((V.rank : ℂ) / 2) with hc0
  have hpt : ∀ (z : ℂ) (b' : hermA D n),
      npow (H (w * nb (cg a (b' - b1)) * (m * u * k))) (z - s0 V n) * Jt ψ V μ (ω (m * u * k) Φ).1 (cg a (b' - b1)) *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) (cg a (b' - b1)).1 : Mx D n n))) =
      (npow A (s0 V n - z) * (c0 * npow A (-(V.rank : ℂ))) * ct) *
        (npow (H (w * nb b' * k)) (z - s0 V n) * Jt ψ V μ φ0.1 b' *
          ψ (-halfTr (Matrix.trace (HMul.hMul T b'.1 : Mx D n n)))) := by
    intro z b'
    have e : w * nb (cg a (b' - b1)) * (m * u * k) = m' * (w * nb b' * k) := by
      calc _ = w * (nb (cg a (b' - b1)) * m) * u * k := by simp only [mul_assoc]
        _ = w * (m * nb (b' - b1)) * u * k := by rw [nb_cg_mul hnb a hm]
        _ = (w * m) * (nb (b' - b1) * nb b1) * k := by rw [hub]; simp only [mul_assoc]
        _ = m' * w * nb b' * k := by rw [hwm, ← nb_add hnb, sub_add_cancel]
        _ = _ := by simp only [mul_assoc]
    have hHe : H (w * nb (cg a (b' - b1)) * (m * u * k)) = A⁻¹ * H (w * nb b' * k) := by
      rw [e, height_mul hH hm'P (ad a) hblk, absA_ad]
    have hJ : Jt ψ V μ (ω (m * u * k) Φ).1 (cg a (b' - b1)) = c0 * (npow A (-(V.rank : ℂ)) * Jt ψ V μ φ0.1 b') := by
      rw [hωe, jt_step hω hμ a hm hu φ0 (b' - b1), sub_add_cancel]
    have e1 : Matrix.trace (HMul.hMul (β.1.map (incA D)) (cg a (b' - b1)).1 : Mx D n n) =
        Matrix.trace (T * (b' - b1).1) := trace_beta a _ _
    have e2 : Matrix.trace (T * (b' - b1).1) = Matrix.trace (T * b'.1) + -Matrix.trace (T * b1.1) := by
      have : (b' - b1).1 = b'.1 - b1.1 := rfl
      rw [this, Matrix.mul_sub, Matrix.trace_sub, sub_eq_add_neg]
    have hch : ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) (cg a (b' - b1)).1 : Mx D n n))) =
        ψ (-halfTr (Matrix.trace (HMul.hMul T b'.1 : Mx D n n))) * ct := by
      rw [e1, e2, halfTr_add, halfTr_neg, neg_add, neg_neg, AddChar.map_add_eq_mul]
    rw [hHe, hJ, hch, npow_mul', npow_inv' hA, show -(z - s0 V n) = s0 V n - z from neg_sub z (s0 V n)]
    ring
  have hint : ∀ z : ℂ, (∫ b, npow (H (w * nb b * (m * u * k))) (z - s0 V n) * Jt ψ V μ (ω (m * u * k) Φ).1 b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam) =
      npow A (s0 V n - z) * ((npow A (n : ℂ) * (c0 * npow A (-(V.rank : ℂ))) * ct) *
        whitT ψ V μ lam nb w H φ0.1 T k z) := by
    intro z
    set Gz : hermA D n → ℂ := fun b => npow (H (w * nb b * (m * u * k))) (z - s0 V n) * Jt ψ V μ (ω (m * u * k) Φ).1 b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) with hGz
    have h1 : ∫ c, Gz (cg a c) ∂lam = npow A (-(n : ℂ)) * ∫ b, Gz b ∂lam := GlobalTheory.CompanionTheory.CgMod.integral_cg D n lam hl a Gz
    have h2 : ∫ x, Gz (cg a (x - b1)) ∂lam = ∫ c, Gz (cg a c) ∂lam :=
      integral_shift_herm lam hl (fun c => Gz (cg a c)) b1
    have h3 : ∫ x, Gz (cg a (x - b1)) ∂lam =
        (npow A (s0 V n - z) * (c0 * npow A (-(V.rank : ℂ))) * ct) * whitT ψ V μ lam nb w H φ0.1 T k z := by
      simp only [hGz, hpt, integral_const_mul]
      rfl
    have h4 : npow A (n : ℂ) * npow A (-(n : ℂ)) = 1 := by
      rw [← npow_add' hA, add_neg_cancel, npow_zero' A hA]
    rw [h3, h1] at h2
    calc ∫ b, Gz b ∂lam = (npow A (n : ℂ) * npow A (-(n : ℂ))) * ∫ b, Gz b ∂lam := by rw [h4, one_mul]
      _ = npow A (n : ℂ) * (npow A (-(n : ℂ)) * ∫ b, Gz b ∂lam) := by ring
      _ = _ := by rw [← h2]; ring
  have h0 := hK D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  have hc := (holValueAt_const (npow A (n : ℂ) * (c0 * npow A (-(V.rank : ℂ))) * ct) (s0 V n)).mul h0
  have hfin := holValueAt_npow_sub_mul _ (fun z => ∫ b, npow (H (w * nb b * (m * u * k))) (z - s0 V n) *
      Jt ψ V μ (ω (m * u * k) Φ).1 b * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam)
    (s0 V n) _ A 0 hA hc (fun z _ => hint z)
  have hval : npow A (n : ℂ) * (c0 * npow A (-(V.rank : ℂ))) * ct *
      (npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
        IfrB V ν (fun x => (ω k Φ).1 (HMul.hMul x a.1)) β) = IfrB V ν (ω (m * u * k) Φ).1 β := by
    have h5 : npow A (n : ℂ) * npow A (-(V.rank : ℂ)) * npow A ((V.rank : ℂ) - n) = 1 := by
      rw [← npow_add' hA, ← npow_add' hA]
      have : (n : ℂ) + -(V.rank : ℂ) + ((V.rank : ℂ) - n) = 0 := by ring
      rw [this, npow_zero' A hA]
    have h6 : ψ (halfTr (Matrix.trace (b1.1 * T))) = ct := by
      rw [hct, Matrix.trace_mul_comm]
    rw [hωe, ifrB_step hω ν a hm hu φ0 β, ← hAdef, ← hT, ← hc0, h6]
    calc _ = (npow A (n : ℂ) * npow A (-(V.rank : ℂ)) * npow A ((V.rank : ℂ) - n)) * (c0 * ct *
            IfrB V ν (fun x => φ0.1 (HMul.hMul x a.1)) β) := by ring
      _ = _ := by rw [h5, one_mul]
  rw [hval] at hfin
  exact hfin

theorem iwaRedA : GlobalTheory.CompanionTheory.IwaAd.WhitKA → PositivityTheory.PfSWUS.WhitNDg := by
  intro hK D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ g
  obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n g
  obtain ⟨a, ha⟩ := exists_blkA hp
  obtain ⟨m, u, b, rfl, hm, hu⟩ := exists_levi_unip hp a ha
  have hbh : adj b = b := (exists_unip b).1 ⟨u, hu⟩
  exact whit_step hK hS hR hC hw hβ a hk hm ⟨b, hbh⟩ hu

end GlobalTheory.CompanionTheory.IwaAd
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.OneSat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_unifU : valuation k ((Zls.unifU k : kˣ) : k) = uniformizer k := by
  have hϖ := Zls.irreducible_unif (k := k)
  apply le_antisymm
  · exact le_uniformizer_iff.2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hϖ.not_isUnit)
  · obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
    have hlt : valuation k y < 1 := hy ▸ uniformizer_lt_one
    rw [← hy]
    exact (mem_cball_uniformiser hϖ (x := Zls.unifU k) rfl ⟨y, hlt.le⟩).2
      (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hlt)

theorem hasSatake_of_equiv {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W} {α : Fin n → ℂˣ}
    (φ : π.Equiv σ) (h : HasSatake π α) : HasSatake σ α := by
  refine ⟨GlobalTheory.Parabolic.isIrreducible_of_equiv φ h.1, ?_, ?_⟩
  · obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 h.2.1
    refine (Submodule.ne_bot_iff _).2 ⟨φ v, fun g => ?_, fun e => h0 (φ.toLinearEquiv.injective ?_)⟩
    · have h1 := hv g
      have e : φ (π g v) = σ g (φ v) := φ.toIntertwiningMap.isIntertwining _ _ g v
      rw [← e, h1, map_smul]
    · simpa using e
  · exact (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans h.2.2

theorem isUnramChar_of_isCusp_of_isSpherical [CharZero k] (x : IrrGL (k := k)) (hx : x.IsCusp) (hs : IsSpherical x.rep) :
    x.IsUnramChar := by
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hadm : IsAdmissible x.rep := (hBZ k).1 (Fin x.1) x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr
  have hI : fixed x.rep (iwahori k (Fin x.1)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm x.2.rep.irr hI
  have hχ : ∀ i, IsSmoothChar (unrChar k (α i)) := fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))
  have h1 := GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => unrChar k (α i)) hχ x.2.rep hα
  have h2 : HasSupport x.rep {x} := hasSupport_self hx
  have he := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma hBZ h1 h2
  have hmem : x ∈ (Finset.univ.val.map fun i => IrrGL.ofChar (unrChar k (α i)) (hχ i)) := by
    rw [he]; exact Multiset.mem_singleton_self x
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
  exact ⟨unrChar k (α i), isUnram_unrChar k (α i), hi.symm⟩

theorem len_eq_one [CharZero k] (Δ : Segment k) (y : IrrGL (k := k)) (hL : IsLSeg Δ y.rep) (hS : IsSpherical y.rep) :
    Δ.len = 1 := by
  have hLM := PositivityTheory.Exh.langlandsMultisegments_holds
  have hSC := PositivityTheory.Exh.standardCosocleGL_holds
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  obtain ⟨N, c⟩ := y
  obtain ⟨hd, hc⟩ := id hL
  have hsub : IsSubquotient c.rep.ρ (prodIrr Δ.term hd) := hc.isSubquotient
  have hsph := GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k Δ.len N Δ.term hd _ c.rep.ρ hsub hS
  have h0 : Δ.term ⟨0, Δ.len_pos⟩ = Δ.first := by simp [Segment.term]
  have key : ∀ x z : IrrGL (k := k), x = z → IsSpherical x.rep → IsSpherical z.rep := by
    rintro _ _ rfl h; exact h
  have hU : Δ.first.IsUnramChar :=
    isUnramChar_of_isCusp_of_isSpherical Δ.first Δ.isCusp_first (key _ _ h0 (hsph _))
  obtain ⟨μ, hμ, hfirst⟩ := hU
  have hμs := isSmoothChar_of_isUnram hμ
  have hterm : ∀ a, Δ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by simp only [Segment.term, IrrGL.nu, hfirst, IrrGL.tw_ofChar]
  have hd1 : Δ.d = 1 := congrArg Sigma.fst hfirst
  have hN : N = Δ.len := by
    have h2 : ∑ a, (Δ.term a).1 = N := hd
    rw [Segment.sum_term_fst, Segment.deg, hd1, mul_one] at h2
    exact h2.symm
  subst hN
  let Γ := Segment.ofChar μ hμs Δ.len Δ.len_pos
  have hterm' : ∀ a, Γ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by
      show (IrrGL.ofChar μ hμs).nu _ = _
      simp only [IrrGL.nu, IrrGL.tw_ofChar]
  have hd' : ∑ a, (Γ.term a).1 = Δ.len := (Segment.sum_term_fst _).trans (mul_one _)
  have hP := GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries Δ.term hd _ _ hterm
  have hP' := GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries Γ.term hd' _ _ hterm'
  let χ' := μ * absPow k (((Δ.len : ℂ) - 1) / 2)
  have hu' : IsUnram χ' := fun x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  have hχs : IsSmoothChar χ' := isSmoothChar_of_isUnram hu'
  obtain ⟨f, hf⟩ := embeds_detRep_segment hμs Δ.len_pos hd'
  have hϖ := valuation_unifU (k := k)
  have hu : ∀ i : Fin Δ.len, IsUnram (μ * absPow k ((i : ℕ) : ℂ)) := fun i x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  let α : Fin Δ.len → ℂˣ := fun i => (μ * absPow k ((i : ℕ) : ℂ)) (Zls.unifU k)
  have heq : (fun i => unrChar k (α i)) = fun i : Fin Δ.len => μ * absPow k ((i : ℕ) : ℂ) :=
    funext fun i => (eq_unrChar (hu i) hϖ).symm
  have hA : HasSatake c.rep.ρ α := ⟨c.rep.irr, hS, by rw [heq]; exact hsub.trans hP⟩
  have hB : HasSatake (IrrRep.det (Fin Δ.len) χ' hχs).ρ α :=
    ⟨(IrrRep.det (Fin Δ.len) χ' hχs).irr, isSpherical_detRep hu',
      by rw [heq]; exact (IsSubquotient.of_injective f hf).trans hP'⟩
  obtain ⟨E⟩ := GlobalTheory.T.nonempty_equiv_of_same_satakeParameters hBZ k Δ.len α c.rep (IrrRep.det (Fin Δ.len) χ' hχs) hA hB
  have hL2 := (GlobalTheory.T.isLanglandsClassification_detCharacter hSC k Δ.len χ' hχs).of_equiv E.symm
  have hL1 := hL.isL
  have hm := (hLM k).1 _ _ ⟨Δ.len, c⟩ hL1 hL2
  have := congrArg Multiset.card hm
  simpa using this.symm

theorem isL_single_unrChar [CharZero k] (x : IrrGL (k := k)) (α : Fin x.1 → ℂˣ) (hsat : HasSatake x.rep α) :
    IsL (Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (unrChar k (α i))
      (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _)) x.rep := by
  obtain ⟨𝔪, hL⟩ := PositivityTheory.Exh.langlandsExhaustionGL_holds k x
  obtain ⟨h, y, hd, ⟨Δ, hord, hseg⟩, hcos⟩ := id hL
  have hsphy : ∀ a, IsSpherical (y a).rep :=
    GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k h x.1 y hd x.2.rep.V x.rep hcos.isSubquotient hsat.2.1
  have hlen : ∀ i, (Δ i).len = 1 := fun i => len_eq_one (Δ i) (y i) (hseg i) (hsphy i)
  have hsingle : ∀ i, Δ i = Segment.single (Δ i).first (Δ i).isCusp_first := fun i =>
    Segment.ext_first rfl (by rw [hlen i]; rfl)
  have hms : ∀ i, (Δ i).ms = {(Δ i).first} := fun i =>
    (congrArg Segment.ms (hsingle i)).trans (Segment.ms_single _ _)
  have h1 : HasSupport x.rep (∑ a, (Δ a).ms) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun a => (hseg a).hasSupport) x.2.rep.irr
      hcos.isSubquotient
  have h2 := GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => unrChar k (α i))
    (fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))) x.2.rep hsat.2.2
  have heq := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness h1 h2
  have hsupp : (∑ a, (Δ a).ms) = Finset.univ.val.map fun i => (Δ i).first := by
    simp only [hms]
    rw [Finset.sum_eq_multiset_sum]
    exact Multiset.bind_singleton Finset.univ.val fun i => (Δ i).first
  rw [hsupp] at heq
  have hinj : Function.Injective fun D : Segment k => (D.first, D.len) := fun a b e =>
    Segment.ext_first (congrArg Prod.fst e) (congrArg Prod.snd e)
  have hm : 𝔪 = Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (unrChar k (α i))
      (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _) := by
    apply Multiset.map_injective hinj
    have e1 := congrArg (Multiset.map fun ρ : IrrGL (k := k) => (ρ, 1)) heq
    simp only [Multiset.map_map, Function.comp_def] at e1
    rw [← hord.1, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, hlen]
    exact e1
  rw [← hm]
  exact hL

end GlobalTheory.CompanionTheory.OneSat


open GlobalTheory.CompanionTheory.OneSat in
theorem GlobalTheory.CompanionTheory.OneSat.lOneSat : PositivityTheory.SphericalProduct.LOneSat := by
  intro k _ _ _ _ _ n ξ hξ V _ _ π hs
  have hϖ := valuation_unifU (k := k)
  have hms : ∀ (χ χ' : kˣ →* ℂˣ) (h : IsSmoothChar χ) (h' : IsSmoothChar χ') (c) (c'), χ = χ' →
      Segment.single (IrrGL.ofChar χ h) c = Segment.single (IrrGL.ofChar χ' h') c' := by
    rintro χ _ h h' c c' rfl; rfl
  have key : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W), IsSmooth τ →
      HasSatake τ (PositivityTheory.SphericalProduct.atUnif k ξ) → IsL (PositivityTheory.SphericalProduct.msOne ξ hξ) τ := by
    intro W _ _ τ hτ hsat
    have φ := IrrGL.equivOf τ hτ hsat.1
    have h1 := isL_single_unrChar (IrrGL.of τ hτ hsat.1) (PositivityTheory.SphericalProduct.atUnif k ξ) (hasSatake_of_equiv φ hsat)
    have h2 : PositivityTheory.SphericalProduct.msOne ξ hξ = Finset.univ.val.map fun i : Fin n =>
        Segment.single (IrrGL.ofChar (unrChar k (PositivityTheory.SphericalProduct.atUnif k ξ i))
          (isSmoothChar_of_isUnram (isUnram_unrChar k _))) (IrrGL.isCusp_ofChar _ _) :=
      Multiset.map_congr rfl fun i _ => hms _ _ _ _ _ _ (eq_unrChar (hξ i) hϖ)
    rw [h2]
    exact h1.of_equiv φ.symm
  refine ⟨fun hL => ?_, key π hs⟩
  obtain ⟨y, hy⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := k) (PositivityTheory.SphericalProduct.atUnif k ξ)
  have hLy := key y.ρ y.smooth hy
  obtain ⟨h, x, hd, hx, hc⟩ := hL
  have hc' := PositivityTheory.Exh.lOrderFree_of GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k _ h n x hd hx y.ρ hLy
  obtain ⟨e⟩ := hc.unique hc'
  exact hasSatake_of_equiv e hy

end
end
