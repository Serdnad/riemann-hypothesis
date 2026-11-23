module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle202
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle203
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle423
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle092
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle210
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle208
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle211
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.ParamInert

open Formalism.UG (IsUnramInv GU KU qV IsInertAt)

theorem paramBoundOn_nonsplit (hUDI : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert) :
    ∀ D : D7, ParamBoundOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro D A L hL v hv par c hc hc1 w hw
  obtain ⟨⟨C, hC⟩, V, iV, iM, ρ, x, ℓ, hpar, hℓ, hcv⟩ := hc
  have hp := hpar w hw
  refine ⟨hp.card, ?_⟩
  rcases hp with ⟨hs, -⟩ | ⟨hin, τ, ϖ, e, α, hU, he, hsat, hB⟩
  · exact absurd hs hv
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    have h4 := hU.2.2.2.1
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  set ϖu : (w.adicCompletion D.host.E)ˣ := Units.mk0 ϖ hϖ0 with hϖu
  have hU' : IsUnramInv ((ϖu : w.adicCompletion D.host.E)) τ (qV D.host.F v) := hU
  set ρ' : Representation ℂ (GU τ A.rank) V := ρ.comp e.symm.toMonoidHom with hρ'
  have hKinv : ∀ k ∈ KU τ A.rank, ∀ g, ℓ (ρ' (k * g) x) = ℓ (ρ' g x) := by
    intro k hk g
    have hk' : e.symm k ∈ stabLoc D.sp.cm.sig A.gram L v := by
      rw [he.2.2, MulEquiv.apply_symm_apply]; exact hk
    simp only [hρ', MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, map_mul]
    rw [← map_mul]
    exact hℓ _ hk' _
  have h1 : ℓ x ≠ 0 := by
    intro h0; apply hc1; rw [hcv, map_one]; exact h0
  have hz := (GlobalTheory.T.invariant_sphericalCoefficient_eq_zero_or_zonal _ ϖu τ (qV D.host.F v) A.rank hU' V ρ' x α hsat ℓ hKinv).2 h1
  have hbd : ∃ C' : ℝ, ∀ g, ‖ℓ (ρ' g x) / ℓ x‖ ≤ C' := by
    refine ⟨C / ‖ℓ x‖, fun g => ?_⟩
    rw [norm_div]
    have : ‖ℓ (ρ' g x)‖ ≤ C := by
      have := hC (e.symm g); rw [hcv] at this; exact this
    exact div_le_div_of_nonneg_right this (norm_nonneg _)
  have htb := GlobalTheory.T.satakeTrivialBound_of_bounded_zonal_spherical_unitary hUDI _ ϖu τ (qV D.host.F v) A.rank hU' α _ hz hbd
  intro β hβ
  rw [hB] at hβ
  have hq2 : 2 ≤ qV D.host.F v := hU.2.2.2.2.2.1
  have hle := GlobalTheory.FinZeta.ParamBound.norm_le_of_mem_bcParam hq2 htb β hβ
  have hnorm : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 :=
    ((GlobalTheory.LFun.exists_isInertChart _ (isCMExt_host D) v).2 w hw hin).2.2.2.1
  have hqv : (qV D.host.F v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := rfl
  rw [hnorm, Nat.cast_pow, ← hqv]
  refine hle.trans (Real.rpow_le_rpow_of_exponent_le ?_ ?_)
  · have : (1 : ℝ) ≤ qV D.host.F v := by exact_mod_cast (by omega : 1 ≤ qV D.host.F v)
    nlinarith
  · linarith

end GlobalTheory.Core.Rk.ParamInert
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Core.Rk.SphSec

section Gen

variable {G : Type} [Group G] (P K : Subgroup G) (f : P →* ℂ)

theorem gen_wd (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (p p' : P) (k k' : G) (hk : k ∈ K) (hk' : k' ∈ K)
    (e : (p : G) * k = p' * k') : f p = f p' := by
  have h1 : ((p'⁻¹ * p : P) : G) = k' * k⁻¹ := by
    have : (p : G) = p' * (k' * k⁻¹) := by rw [← mul_assoc, ← e, mul_inv_cancel_right]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, this, inv_mul_cancel_left]
  have h2 := hK _ (h1 ▸ mul_mem hk' (inv_mem hk))
  calc f p = f (p' * (p'⁻¹ * p)) := by rw [mul_inv_cancel_left]
    _ = f p' := by rw [map_mul, h2, mul_one]

variable (hI : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k)

noncomputable def genFun (g : G) : ℂ := f (hI g).choose

variable {P K f hI}

theorem genFun_mul (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (p : P) {k : G} (hk : k ∈ K) :
    genFun P K f hI (p * k) = f p := by
  obtain ⟨k', hk', e⟩ := (hI (p * k)).choose_spec
  exact gen_wd P K f hK _ _ _ _ hk' hk e.symm

theorem genFun_right (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (g : G) {k : G} (hk : k ∈ K) :
    genFun P K f hI (g * k) = genFun P K f hI g := by
  obtain ⟨k₀, hk₀, e⟩ := (hI g).choose_spec
  conv_lhs => rw [e, mul_assoc]
  exact genFun_mul hK _ (mul_mem hk₀ hk)

theorem genFun_left (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (p : P) (g : G) :
    genFun P K f hI (p * g) = f p * genFun P K f hI g := by
  obtain ⟨k₀, hk₀, e⟩ := (hI g).choose_spec
  conv_lhs => rw [e, ← mul_assoc]
  rw [← Subgroup.coe_mul, genFun_mul hK _ hk₀, map_mul]
  rfl

theorem genFun_one (hK : ∀ p : P, (p : G) ∈ K → f p = 1) : genFun P K f hI 1 = 1 := by
  have := genFun_mul (hI := hI) hK 1 (one_mem K)
  rwa [Subgroup.coe_one, mul_one, map_one] at this

theorem genFun_unique (Ψ : G → ℂ) (hΨ : ∀ (p : P) g, Ψ (p * g) = f p * Ψ g) (hΨK : ∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g)
    (g : G) : Ψ g = Ψ 1 * genFun P K f hI g := by
  obtain ⟨k₀, hk₀, e⟩ := (hI g).choose_spec
  have := hΨ (hI g).choose 1
  rw [mul_one] at this
  rw [genFun, mul_comm]
  conv_lhs => rw [e]
  rw [hΨK _ hk₀, this]

theorem continuous_genFun [TopologicalSpace G] [IsTopologicalGroup G] (hK : ∀ p : P, (p : G) ∈ K → f p = 1)
    (ho : IsOpen (K : Set G)) : Continuous (genFun P K f hI) := by
  refine continuous_iff_continuousAt.2 fun g => (continuousAt_const (y := genFun P K f hI g)).congr ?_
  filter_upwards [(ho.preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp [one_mem])] with h hh
  have := genFun_right (hI := hI) hK g (k := g⁻¹ * h) hh
  rwa [mul_inv_cancel_left, eq_comm] at this

theorem gen_exists [TopologicalSpace G] [IsTopologicalGroup G] (P K : Subgroup G) (f : P →* ℂ)
    (hI : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (ho : IsOpen (K : Set G)) :
    ∃ φ : G → ℂ, (∀ (p : P) g, φ (p * g) = f p * φ g) ∧ Continuous φ ∧ (∀ g, ∀ k ∈ K, φ (g * k) = φ g) ∧ φ 1 = 1 ∧
      ∀ Ψ : G → ℂ, (∀ (p : P) g, Ψ (p * g) = f p * Ψ g) → (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∀ g, Ψ g = Ψ 1 * φ g :=
  ⟨genFun P K f hI, genFun_left hK, continuous_genFun hK ho, fun g _ hk => genFun_right hK g hk, genFun_one hK,
    fun Ψ hΨ hΨK g => genFun_unique Ψ hΨ hΨK g⟩

end Gen



theorem exists_isSphSecAt_unique : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ v : FinPl D, (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt μ w) → ∀ s : ℂ, ∃ φ, IsSphSecAt A L v μ s φ ∧ ∀ Ψ : Gv (dblSp A) v → ℂ, (∀ (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram) g, Ψ (p * g) = charAt μ v (aH _ D.sp.cm.sig (dblSp A).gram p) * npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) * Ψ g) → (∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram L v, ∀ g, Ψ (g * k) = Ψ g) → ∀ g, Ψ g = Ψ 1 * φ g := by
  intro D A L hL μ hμ v hunr s
  haveI : Submodule.IsFullLattice D.host.E L :=
    Formalism.IndefR.Fin.PDA.selfDual_isFullLattice A L hL
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
    by_cases hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
    · exact GlobalTheory.T.hasIwasawaDecomposition_doubled_split_place D A L hL v hs
    · exact GlobalTheory.T.iwasawa_doubled_hermitian_space_nonsplit_place D A L hL v hs
  let N : ℝ≥0 →* ℂ := ⟨⟨fun r => npow r (s + (A.rank : ℂ) / 2), one_npow _⟩, fun r r' => GlobalTheory.Doubling.npow_mul r r' _⟩
  let f : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram →* ℂ :=
    (Circle.coeHom.comp ((charAt μ v).comp (aH _ D.sp.cm.sig (dblSp A).gram))) *
      (N.comp ((absEv D.host.F D.host.E v).comp (aH _ D.sp.cm.sig (dblSp A).gram)))
  have hf : ∀ p, f p = (charAt μ v (aH _ D.sp.cm.sig (dblSp A).gram p) : ℂ) *
      npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) := fun p => rfl
  have hK : ∀ p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram,
      (p : Gv (dblSp A) v) ∈ KFin D.sp.cm.sig (dblSp A).gram L v → f p = 1 := by
    intro p hp
    have h1 := GlobalTheory.T.siegelLeviDeterminant_integral_selfDual_lattice D A L hL v p hp
    have h2 : (((aH _ D.sp.cm.sig (dblSp A).gram p)⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) :
        Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v := by
      rw [← map_inv]
      exact GlobalTheory.T.siegelLeviDeterminant_integral_selfDual_lattice D A L hL v p⁻¹ (inv_mem hp)
    rw [hf, GlobalTheory.T.ideleCharacter_eq_one_integral_units_unramified_adelic D μ v _ h1 h2 hunr,
      abs_aH_eq_one (continuous_absEv v) (isCompact_KFin v) p hp, one_npow, Circle.coe_one, one_mul]
  clear_value f
  obtain ⟨φ, hl, hc, hr, h1, hu⟩ := gen_exists (G := Gv (dblSp A) v) _ _ f hI hK (isOpen_KFin v)
  refine ⟨φ, ⟨mem_degPSH.2 ⟨fun p g => by rw [hl, hf], hc, IsKFinite.of_invariant fun g k hk => hr g k hk⟩,
    fun k hk g => hr g k hk, h1⟩, fun Ψ hΨ hΨK g => hu Ψ (fun p g => by rw [hΨ, hf]) hΨK g⟩

end GlobalTheory.Core.Rk.SphSec

end
end

section

noncomputable section

namespace GlobalTheory.Core.Rk.KerSplit

section General

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LFun
open Formalism.UG (ordL)
open Formalism.L2.Host (atFin unif unif_spec IsUnifAt IsUnitAt)

theorem locChar_eq_val_zpow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ : (AF F ⊗[F] E)ˣ →* Circle} {w : HeightOneSpectrum (𝓞 E)} (h : UnrAt χ w) (y : (w.adicCompletion E)ˣ) :
    locChar χ w y = val χ w ^ ordL y.1 := by
  have hy : Valued.v y.1 ≠ 0 := by simp
  have h0 : Valued.v y.1 = WithZero.exp (-ordL y.1) := by
    rw [ordL, dite_eq_right hy, neg_neg]
    exact (WithZero.coe_unzero hy).symm
  have h1 : IsUnitAt w (y * (atFin w (unif w)) ^ (-ordL y.1)) := by
    have := unif_spec w
    unfold IsUnifAt at this
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, this, ← WithZero.exp_zsmul]
    nth_rewrite 1 [h0]
    rw [← WithZero.exp_add]
    simp
  have := h _ h1
  rwa [map_mul, map_zpow, zpow_neg, mul_inv_eq_one] at this

theorem npow_zpow_neg {r : ℝ≥0} {q : ℕ} {m : ℤ} (h : (r : ℝ) = (q : ℝ) ^ (-m)) (z : ℂ) :
    GlobalTheory.Doubling.npow r z = (q : ℂ) ^ (-z * (m : ℂ)) := by
  rw [GlobalTheory.Doubling.npow, h, Complex.ofReal_zpow, Complex.ofReal_natCast, ← Complex.cpow_intCast,
    ← Complex.cpow_mul]
  · congr 1; push_cast; ring
  · rw [← Complex.natCast_log, Complex.mul_im, Complex.ofReal_im, Complex.intCast_im]; simp [Real.pi_pos]
  · rw [← Complex.natCast_log, Complex.mul_im, Complex.ofReal_im, Complex.intCast_im]; simp [Real.pi_pos.le]


open GlobalTheory.AdelicU GlobalTheory.Doubling Formalism.UG in

theorem char_value {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hc : IsCMExt F E σ) {χ : (AF F ⊗[F] E)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 F)}
    {w w' : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) (hne : w ≠ w')
    (hall : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') (hU : UnrAt χ w) (hU' : UnrAt χ w')
    (hm : val χ w * val χ w' = 1) {n : ℕ} (d : Fin n → ℤ) (x : (Fv F v ⊗[F] E)ˣ)
    (o1 : ordL (toCompl h x.1) = ∑ i, max (d i) 0) (o2 : ordL (toCompl h' x.1) = -∑ i, min (d i) 0) (z : ℂ) :
    ((charAt χ⁻¹ v x : Circle) : ℂ) * GlobalTheory.Doubling.npow (absEv F E v x) z =
      (((val χ w)⁻¹ : ℂˣ) : ℂ) ^ (∑ i, d i) * (qV E w : ℂ) ^ (-z * ((∑ i, |d i| : ℤ) : ℂ)) := by
  have habs := GlobalTheory.T.norm_cmExtension_splitPlace_eq_zpow _ _ _ hc v w h w' h' hne x
  have hch := GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_mul_of_split _ _ χ⁻¹ v w h w' h' hne hall x
  have s1 : ∑ i, max (d i) 0 + -∑ i, min (d i) 0 = ∑ i, |d i| := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [abs_eq_max_neg]; omega
  have s2 : ∑ i, max (d i) 0 + ∑ i, min (d i) 0 = ∑ i, d i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by omega
  rw [o1, o2, s1] at habs
  rw [locChar_eq_val_zpow hU.inv, locChar_eq_val_zpow hU'.inv, val_inv, val_inv, ← Units.val_mul] at hch
  change _ = (((val χ w)⁻¹ ^ ordL (toCompl h x.1) * (val χ w')⁻¹ ^ ordL (toCompl h' x.1) : ℂˣ) : ℂ) at hch
  rw [o1, o2, eq_inv_of_mul_eq_one_right hm, inv_inv, zpow_neg (val χ w), ← inv_zpow, ← zpow_add, s2,
    Units.val_zpow_eq_zpow_val] at hch
  rw [hch, npow_zpow_neg habs]

end General

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt)



theorem sphSec_split : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), ResEta D χ b → ∀ v : FinPl D, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χ w) → ∀ (s : ℂ) (φ : Gv (dblSp A) v → ℂ), IsSphSecAt A L v χ⁻¹ s φ → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (e : Gv A v ≃* GL (Fin A.rank) (w.adicCompletion D.host.E)), IsSplitChart D.sp.cm.sig A.gram L h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin A.rank → ℤ) (t : GL (Fin A.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := A.rank), ∀ k₂ ∈ KGL w (n := A.rank), φ (ioAt A v (e.symm (k₁ * t * k₂))) = (((GlobalTheory.LFun.val χ w)⁻¹ : ℂˣ) : ℂ) ^ (∑ i, d i) * (qV D.host.E w : ℂ) ^ (-((A.rank : ℂ) / 2 + s) * ((∑ i, |d i| : ℤ) : ℂ)) := by
  intro D A L hL χ b hχ v hv hU s φ hφ w h e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  haveI := hL.1
  have hc := isCMExt_host D
  obtain ⟨w', hne, hall, -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place hc h hv
  have h' : w'.under (𝓞 D.host.F) = v := (hall w').2 (Or.inr rfl)
  have hm : GlobalTheory.LFun.val χ w * GlobalTheory.LFun.val χ w' = 1 :=
    GlobalTheory.LFun.ResEta.val_mul_val hc.2.2.1 ((GlobalTheory.LFun.resEta_iff χ _).1 hχ) hne h h' (hU w h) (hU w' h')
  obtain ⟨f, hfK, hfi, hfP, hfa⟩ := GlobalTheory.T.exists_doubled_unitary_chart_split_place _ _ _ hc A.rank A.gram (GlobalTheory.Doubling.isHermND_gram A) (dblSp A).gram
    (gram_hdbl A) L v w h hv (IwSplit.isSelfDualAt_of_isSelfDualC hL v) e he
  obtain ⟨κ, hκ, hP, hl, hq⟩ := GlobalTheory.T.exists_integral_keepsDoublingDiagonal_adicCompletion _ w A.rank ϖ hϖ d t k₁ k₂ ht hk₁ hk₂
  have hp : f (ioAt A v (e.symm (k₁ * t * k₂)) * f.symm κ) = blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ := by
    rw [map_mul, f.apply_symm_apply, ioAt, hfi, e.apply_symm_apply, map_one]
  rw [← hp] at hP hl hq
  rw [← hφ.2.1 (f.symm κ) ((hfK _).2 (by rwa [f.apply_symm_apply]))]
  generalize ioAt A v (e.symm (k₁ * t * k₂)) * f.symm κ = g at hP hl hq ⊢
  obtain ⟨ha, ha'⟩ := hfa ⟨g, (hfP g).2 hP⟩
  have ha' := ha' w' h' hne
  have law := (mem_degPSH.1 hφ.1).1 ⟨g, (hfP g).2 hP⟩ 1
  generalize aH _ D.sp.cm.sig (dblSp A).gram ⟨g, (hfP g).2 hP⟩ = x at ha ha' law
  have o1 : Formalism.UG.ordL (GlobalTheory.LFun.toCompl h x.1) = ∑ i, max (d i) 0 := by rw [ha]; exact hl
  have o2 : Formalism.UG.ordL (GlobalTheory.LFun.toCompl h' x.1) = -∑ i, min (d i) 0 := by rw [ha']; exact congrArg _ hq
  rw [mul_one, hφ.2.2, mul_one] at law
  refine law.trans ?_
  rw [add_comm ((A.rank : ℂ) / 2) s]
  exact char_value hc h h' hne hall (hU w h) (hU w' h') hm d x o1 o2 _

end GlobalTheory.Core.Rk.KerSplit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

theorem _root_.GlobalTheory.T.exists_charts_at_twist_places_chain : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, (∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP) ∧ ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → (∃ e, IsIdemOf φ e) ∧ (∃ x ϖ, IsLocUnif φ x ϖ) ∧ (∃ ι, IsChart s j φ ι) ∧ ∀ χ : (AE D)ˣ →* Circle, ∃ μ : (Fv D.host.F v)ˣ →* ℂˣ, GlobalTheory.SmGL.IsUnitaryChar μ ∧ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (χ x)) := by
  first | exact @GlobalTheory.TwistChart.charts_at_twist | exact GlobalTheory.TwistChart.charts_at_twist | (intros; apply GlobalTheory.TwistChart.charts_at_twist <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

theorem _root_.GlobalTheory.T.exists_topological_iso_parahoric_chart_split_place : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∃ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) ≃ₜ* GlobalTheory.FinZeta.Gv s.V v, ∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y) := by
  first | exact @GlobalTheory.ChartSplitIso.exists_equiv_emb | exact GlobalTheory.ChartSplitIso.exists_equiv_emb | (intros; apply GlobalTheory.ChartSplitIso.exists_equiv_emb <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.UnfLink

theorem star_psi {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem heisO_at_zero' {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  have h : hO S T 0 w = 0 := by simp [hO]
  simp [heisO, symplOH, symplO, h]

theorem link : ∀ D : D7, LinkLaw D := by
  intro D ψ ρ B J s L' ζ' hz l φ Ξ hφ hΞ
  refine ⟨GlobalTheory.T.besselToFourierJacobi_handedFamily_continuous_automorphic D ψ ρ B J s L' ζ' hz l φ Ξ hφ hΞ, fun G' => ?_⟩
  unfold JacLev.perAll JacLev.per fjAll fjSrcKer
  congr 1; funext h; congr 1; funext n
  have hk := GlobalTheory.T.fourierJacobiKernel_eq_weilRepresentation_apply D ψ J.W J.W₀ B.V₀ B.A B.L ρ J.d B.o B.ζ _ _ s.om₀ s.weil₀ Ξ hΞ
  obtain ⟨hp, hc⟩ := GlobalTheory.T.jacobiActions_match_through_linkMap D ρ ρ B L' ζ' hz l J.W J.W₀ J.d n.1 n.2
  simp only [fjAllFun, fjSrcKerFun, JacLev.ker, jacS, handBF, hk, Pi.smul_apply, smul_eq_mul, heisO_at_zero', hp, hc]
  rw [star_mul', star_star, star_psi s.weil₀.std]
  simp_rw [mul_left_comm (φ _) (ψ _)]
  rw [integral_const_mul]
  ring

end GlobalTheory.UnfLink
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ContrComb

theorem contr_quasi : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → (∀ γ u v, contr l S vL f₁ f₂ (ratW S B.A γ + u) v = ψ (-(symplOH B.A S (ratW S B.A γ) u)) * contr l S vL f₁ f₂ u v) ∧ ∀ γ u v, contr l S vL f₁ f₂ u (ratW B'.A S γ + v) = ψ (-(symplOH S B'.A (ratW B'.A S γ) v)) * contr l S vL f₁ f₂ u v := by
  intro D ρ σ B B' l S vL ψ f₁ f₂ h₁ h₂
  constructor
  · intro γ u v
    have e0 : (B.o.resS S).symm (ratW S B.A γ, 0) = ratW S B.V₀ (γ * B.o.qA) := by
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    simp only [contr]
    rw [← integral_const_mul]
    congr 1
    funext w
    have e : ((ratW S B.A γ + u, l.κ S w) : WO B.A S × WO B.L S) = (ratW S B.A γ, (0 : WO B.L S)) + (u, l.κ S w) := by simp
    rw [e, map_add (f := _), e0, h₁.quasi, ← e0, B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      symplOH_zero_left, add_zero]
    ring
  · intro γ u v
    have e0 : (B'.o.resT S).symm (ratW B'.A S γ, 0) = ratW B'.V₀ S (B'.o.iA * γ) := by
      rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    simp only [contr]
    rw [← integral_const_mul]
    congr 1
    funext w
    have e : ((ratW B'.A S γ + v, w) : WO S B'.A × WO S B'.L) = (ratW B'.A S γ, (0 : WO S B'.L)) + (v, w) := by simp
    rw [e, map_add (f := _), e0, h₂.quasi, ← e0, B'.o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      symplOH_zero_left, add_zero]
    ring

end GlobalTheory.ContrComb
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.flagUnipotentHaar_eq_map_coordinates : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure → SFinite lC → IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC → lC 𝓒 = 1 → vN.ν = (lC.prod (vb.μ.prod vU.ν)).map e := by
  first | exact @GlobalTheory.HaarCoordsUnit.volN_eq_map_coords | exact GlobalTheory.HaarCoordsUnit.volN_eq_map_coords | (intros; apply GlobalTheory.HaarCoordsUnit.volN_eq_map_coords <;> assumption)
end
