module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle321
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle580
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle021
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThB
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle011
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
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

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LJPos

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (tensNU tensNU_tmul)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

def pkgOf (D : D7) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : SplitPkg D v where
  π := splitAlgEquiv (isCMExt_host D) τ
  swap := splitAlgEquiv_sigR (isCMExt_host D) τ
  int := fun _ => mem_intLoc_iff_split (isCMExt_host D) τ

theorem sigR_tensNU {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (σ : E →ₐ[F] E) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (y : R ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R' σ (tensNU j hj y) = tensNU j hj (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem conjUnit_ideleAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : (Fv F v ⊗[F] E)ˣ) :
    conjUnit σ (ideleAt F E v w) = ideleAt F E v (conjUnit σ w) := by
  refine Units.ext ?_
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (1 - tensNU (inFin v) (inFin_mul v) 1 + tensNU (inFin v) (inFin_mul v) w.1) =
    1 - tensNU (inFin v) (inFin_mul v) 1 + tensNU (inFin v) (inFin_mul v) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ w.1)
  rw [map_add (f := _), map_sub, map_one, sigR_tensNU, sigR_tensNU, map_one]

theorem resEta_norm {D : D7} {χ : (AE D)ˣ →* Circle} {r : ℕ} (h : ResEta D χ r) (x : (AE D)ˣ) :
    χ (x * conjUnit D.sp.cm.sig x) = 1 := by
  obtain ⟨⟨η, hη⟩, h2⟩ := h
  have e : x * conjUnit D.sp.cm.sig x =
      idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) x) :=
    Units.ext (algebraMap_norm_eq (isCMExt_host D) x.1).symm
  rw [e, h2 η hη, hη.2.2.1, one_pow]

theorem diag_eq_norm {D : D7} {v : Pl D} (P : SplitPkg D v) (u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)
    (hu : (P.π u).1 = (P.π u).2) : ∃ w, u = w * conjUnit D.sp.cm.sig w := by
  have h1 : (P.π u).1 * (P.π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).1 = 1 := by
    rw [← Prod.fst_mul, ← map_mul, Units.mul_inv, map_one, Prod.fst_one]
  refine ⟨⟨P.π.symm ((P.π u).1, 1), P.π.symm ((P.π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).1, 1), ?_, ?_⟩,
    Units.ext (P.π.injective ?_)⟩
  · rw [← map_mul, Prod.mk_mul_mk, h1, mul_one]; exact map_one _
  · rw [← map_mul, Prod.mk_mul_mk, mul_comm, h1, mul_one]; exact map_one _
  · change _ = P.π (P.π.symm ((P.π u).1, 1) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig (P.π.symm ((P.π u).1, 1)))
    rw [map_mul, P.swap, AlgEquiv.apply_symm_apply]
    exact Prod.ext (by simp) (by simp [hu])

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : HeightOneSpectrum (𝓞 F)}

omit [NumberField E] in
theorem snd_tensNU_mem {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (tensNU (inFin v) (inFin_mul v) y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  refine intLoc_induction (p := fun y => Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
      (tensNU (inFin v) (inFin_mul v) y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)})
    (fun a ha x => AddSubgroup.subset_closure ⟨singleFin v a, fun w => ?_, x, rfl⟩) ?_ (fun y z hy hz => ?_)
    (fun y hy => ?_) hy
  · by_cases hw : w = v
    · subst hw; rw [evalV_singleFin_self]; exact ha
    · rw [evalV_singleFin_ne hw]; exact zero_mem _
  · rw [map_zero, map_zero]; exact zero_mem _
  · rw [map_add (f := _), map_add (f := _)]; exact add_mem hy hz
  · rw [map_neg, map_neg]; exact neg_mem hy

omit [NumberField E] in
theorem snd_ideleAt_mem {u : (Fv F v ⊗[F] E)ˣ} (hu : u.1 ∈ intLoc F E v) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (ideleAt F E v u).1 ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  rw [ideleAt, val_extUnit, map_add (f := _), map_sub, map_one]
  exact add_mem (sub_mem (AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, 1, rfl⟩)
    (snd_tensNU_mem (one_mem _))) (snd_tensNU_mem hu)

omit [NumberField E] in
theorem eval_snd_ideleAt {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (u : (Fv F v ⊗[F] E)ˣ) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (ideleAt F E v u).1) = 1 := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
  exact map_extUnit_zero _ (inFin v) (inFin_mul v) (fun a => evalV_singleFin_ne hw a) u

omit [NumberField E] in
theorem fst_ideleAt (u : (Fv F v ⊗[F] E)ˣ) :
    Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (ideleAt F E v u).1 = 1 :=
  map_extUnit_zero _ _ _ (fun _ => rfl) u

end Gen

theorem unram_ideleAt {D : D7} {χ : (AE D)ˣ →* Circle} {v : Pl D} (h : CharUnramAt D χ v)
    {u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ} (hu : u.1 ∈ intLoc D.host.F D.host.E v)
    (hu' : (u⁻¹).1 ∈ intLoc D.host.F D.host.E v) : χ (ideleAt D.host.F D.host.E v u) = 1 := by
  refine h _ (fst_ideleAt u) (fun w hw => eval_snd_ideleAt hw u) (snd_ideleAt_mem hu) ?_
  rw [← MonoidHom.map_inv]
  exact snd_ideleAt_mem hu'

theorem placeEx : PlaceEx := by
  classical
  intro D ψ hψ χ hχ r hr S
  have hev := (GlobalTheory.T.character_conductor_condition D.host.F ψ hψ).and (GlobalTheory.FinPl.LastInhab.eventually_charUnramAt D χ hχ.1)
  obtain ⟨v, hv, ⟨τ⟩⟩ := GlobalTheory.Orb.exists_split_place_notMem (isCMExt_host D) (S ∪ (Filter.eventually_cofinite.1 hev).toFinset)
  rw [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
  refine ⟨v, hv.1, pkgOf D v τ, hv.2.1, fun u h1 h2 h3 => ?_, fun u hu => ?_⟩
  · refine unram_ideleAt hv.2.2 (((pkgOf D v τ).int _).2 ⟨h1, by rw [h3]; exact one_mem _⟩)
      (((pkgOf D v τ).int _).2 ⟨h2, ?_⟩)
    have e : ((pkgOf D v τ).π u).2 * ((pkgOf D v τ).π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).2 = 1 := by
      rw [← Prod.snd_mul, ← map_mul, Units.mul_inv, map_one, Prod.snd_one]
    rw [h3, one_mul] at e
    rw [e]; exact one_mem _
  · obtain ⟨w, rfl⟩ := diag_eq_norm _ u hu
    rw [map_mul, ← conjUnit_ideleAt]
    exact resEta_norm hr _

end PositivityTheory.Rg.Rsw.L.LJPos

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

open LFixTh

open Classical in


theorem fixTh : IdemEx → GenG → GenK → FixTh := by
  intro _ hG hK D ρ p m ψ hψ χ hχ θ _ b₀ hb₀
  obtain ⟨S₁, hS₁⟩ := hK D p
  obtain ⟨S₃, hS₃⟩ := LFixW.psi_kernel hψ
  obtain ⟨S₄, hS₄⟩ := LFixW.ft_supp b₀.1 hb₀ hψ
  have hgood := eventually_goodPl hχ b₀
  refine ⟨S₁ ∪ S₃ ∪ S₄ ∪ (Filter.eventually_cofinite.1 hgood).toFinset, fun S hS e he Ω hΩ hgoodΩ => ?_⟩
  have hSg : ∀ v ∉ S, GoodPl χ b₀ v := fun v hv => by
    by_contra h
    exact hv (hS (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h)))
  have hSI := hS₃ S (fun v hv => hS (by simp [hv]))
  have hS4 := hS₄ S (fun v hv => hS (by simp [hv])) e he p m.μ
  have : m.μ.IsAddHaarMeasure := m.hμ.1
  let A' : Set (G D p) := {x | Ω x = Ω 1}
  have hA'c : IsClosed A' := by
    have e : A' = ⋂ y, {x | Ω x y = Ω 1 y} := by
      ext x; simp only [A', Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
    rw [e]
    exact isClosed_iInter fun y => isClosed_eq (hΩ.cont.comp (continuous_id.prodMk continuous_const)) continuous_const
  have hgen : ∀ g ∈ KOff D p S, (IsN g ∨ IsM g ∨ ∃ w u, IsW w ∧ IsN u ∧ u ∈ KOff D p S ∧ g = w * u * w⁻¹) →
      ∀ x ∈ A', g * x ∈ A' := by
    intro g hg hgt x hx
    simp only [A', Set.mem_ofPred_eq] at hx ⊢
    rcases hgt with ⟨b, hb⟩ | ⟨a, ha⟩ | ⟨w, u, hw, ⟨b, hb⟩, hu, rfl⟩
    · funext y
      rw [hΩ.unip g b hb x y, hx]
      by_cases hy : IntOff S y
      · rw [unip_one hSg hSI hg hb hy, one_mul]
      · rw [hgoodΩ y, if_neg hy, mul_zero]
    · have hbl := levi_blocks hg ha
      obtain ⟨h1, h2⟩ := levi_chr hχ hSg a (fun i j w => ((hbl i j).1 w).1) (fun i j v hv => ((hbl i j).2.1 v hv).1)
        (fun i j v hv => (hbl i j).2.2 v hv)
      funext y
      rw [hΩ.levi g a ha x y, hx, h1, h2, levi_good he hg ha _ hgoodΩ y]
      simp [npow]
    · let c : ℂ := (χ (Matrix.GeneralLinearGroup.det (-1 : GL (Fin p) (AE D))) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin p) (AE D)))) ((ρ : ℂ) / 2)
      have hΦ : ∀ y, Ω (w⁻¹ * x) y = ∫ z, (fun z => c * Ω 1 (-z)) z * ψ (trA (pr b₀ y z).trace) ∂m.μ := by
        intro y
        have e1 : w⁻¹ * x = w * ((w * w)⁻¹ * x) := by group
        rw [e1, hΩ.weyl w hw]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [hΩ.levi _ (-1) (mat_ww hw) x z, hx, Units.val_neg, Units.val_one, Matrix.mul_neg, Matrix.mul_one]
      have hzero : ∀ y, ψ (halfTr (b * pr b₀ y y).trace) * Ω (w⁻¹ * x) y = Ω (w⁻¹ * x) y := by
        intro y
        by_cases hy : IntOff S y
        · rw [unip_one hSg hSI hu hb hy, one_mul]
        · rw [hΦ y, show (∫ z, (fun z => c * Ω 1 (-z)) z * ψ (trA (pr b₀ y z).trace) ∂m.μ) = 0 from
            hS4 this _ (good_neg hgoodΩ c) y hy, mul_zero]
      funext y
      have e2 : w * u * w⁻¹ * x = w * (u * (w⁻¹ * x)) := by group
      have e3 : Ω 1 y = Ω (w * (w⁻¹ * x)) y := by rw [mul_inv_cancel_left, hx]
      rw [e2, e3, hΩ.weyl w hw, hΩ.weyl w hw]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only
      rw [hΩ.unip u b hb, hzero z]
  have hK' : (KOff D p S : Set (G D p)) ⊆ A' :=
    hS₁ S (fun v hv => hS (by simp [hv])) A' hA'c rfl hgen
  intro u hu h
  let A : Set (G D p) := {h | Ω (h * u) = Ω h}
  have hAc : IsClosed A := by
    have e : A = ⋂ y, {h | Ω (h * u) y = Ω h y} := by
      ext x; simp only [A, Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
    rw [e]
    exact isClosed_iInter fun y => isClosed_eq
      (hΩ.cont.comp ((continuous_mul_const u).prodMk continuous_const))
      (hΩ.cont.comp (continuous_id.prodMk continuous_const))
  have h1 : (1 : G D p) ∈ A := by
    show Ω (1 * u) = Ω 1
    rw [one_mul]; exact hK' hu
  have hA := hG D p A hAc h1 fun g hgt x hx => by
    show Ω (g * x * u) = Ω (g * x)
    have hx' : Ω (x * u) = Ω x := hx
    rcases hgt with ⟨b, hb⟩ | ⟨a, ha⟩ | hw
    · funext y; rw [mul_assoc, hΩ.unip g b hb, hΩ.unip g b hb, hx']
    · funext y; rw [mul_assoc, hΩ.levi g a ha, hΩ.levi g a ha, hx']
    · funext y; rw [mul_assoc, hΩ.weyl g hw, hΩ.weyl g hw, hx']
  have hh : h ∈ A := hA ▸ Set.mem_univ h
  exact hh

end PositivityTheory.Rg.Rsw.L

end
end
